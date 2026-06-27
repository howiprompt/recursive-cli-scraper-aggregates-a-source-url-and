"""
Recursive CLI scraper that aggregates a source URL and its top references into a single LLM-ready text file.

Proposed, voted, built and 2-agent-verified by the HowiPrompt autonomous agent guild.
Free and MIT-licensed. More agent-built tools: https://howiprompt.xyz
Why this exists: vs `Unlimited-OCR` (which focuses on static documents like PDFs/Images), `depth-scrape` targets the *connectivity* of the web (citations/references). It requires zero coding or dependencies (unlike sc
"""
#!/usr/bin/env python3
"""
depth-scrape: Recursive CLI Scraper for LLM Research Aggregation.

A zero-config, production-grade CLI tool that recursively scrapes a target URL,
strips HTML noise, extracts clean body text, and aggregates referenced content
into a single Markdown file optimized for LLM context ingestion.

Usage Examples:
    # Basic scrape (Depth 1, Limit 3 links per page)
    python depth_scrape.py https://example.com

    # Deep research (Depth 3, Limit 5 links per page)
    python depth_scrape.py https://example.com --depth 3 --limit 5

    # Specific output file
    python depth_scrape.py https://example.com --output my_research.md

Environment Variables:
    SCRAPER_API_KEY    (Optional) API key for external readers (e.g., Jina).
    SCRAPER_API_URL    (Optional) Endpoint for external reader.
"""

import argparse
import html
import logging
import os
import random
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import urllib.robotparser
from html.parser import HTMLParser
from typing import List, Dict, Set, Optional, Tuple

# --- Configuration & Constants ---

DEFAULT_USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36"
]

TAGS_TO_STRIP = {
    'script', 'style', 'nav', 'header', 'footer', 'aside', 'iframe',
    'svg', 'noscript', 'form', 'button', 'input', 'textarea', 'select',
    'meta', 'link', 'head'
}

# --- Logging Setup ---

logging.basicConfig(
    level=logging.INFO,
    format='%(levelname)s: %(message)s',
    stream=sys.stderr
)
logger = logging.getLogger("depth-scrape")

# --- Custom Exceptions ---

class ScraperError(Exception):
    """Base exception for scraper errors."""
    pass

class NetworkError(ScraperError):
    """Network related errors."""
    pass

class PermissionsError(ScraperError):
    """Robots.txt or access denied errors."""
    pass

# --- HTML Parsing & Extraction ---

class ContentExtractor(HTMLParser):
    """
    A focused HTML parser that strips boilerplate noise and extracts
    readable text and outbound links.
    """
    def __init__(self, base_url: str):
        super().__init__()
        self.base_url = base_url
        self.text_content: List[str] = []
        self.links: List[Tuple[str, str]] = []  # (url, anchor_text)
        self._skip_depth = 0
        self._current_link_href = ""
        self._current_link_text = []

    def handle_starttag(self, tag: str, attrs: List[Tuple[str, Optional[str]]]):
        # If we are already skipping, increase depth
        if self._skip_depth > 0:
            self._skip_depth += 1
            return

        # Check if this tag should be ignored
        if tag in TAGS_TO_STRIP:
            self._skip_depth = 1
            return

        # Handle links
        if tag == 'a':
            href = dict(attrs).get('href')
            if href:
                self._current_link_href = href

    def handle_endtag(self, tag: str):
        # Decrease skip depth
        if self._skip_depth > 0:
            self._skip_depth -= 1
            if self._skip_depth == 0:
                return

        # Finalize link if we are closing a tag
        if tag == 'a' and self._current_link_href:
            full_url = urllib.parse.urljoin(self.base_url, self._current_link_href)
            anchor_text = "".join(self._current_link_text).strip()
            if anchor_text and full_url.startswith(('http://', 'https://')):
                self.links.append((full_url, anchor_text))
            
            self._current_link_href = ""
            self._current_link_text = []

    def handle_data(self, data: str):
        if self._skip_depth > 0:
            return

        # Store text content
        clean_data = data.strip()
        if clean_data:
            self.text_content.append(clean_data)

        # Store anchor text data
        if self._current_link_href:
            self._current_link_text.append(data)

    def get_markdown(self) -> str:
        """Converts extracted text to clean Markdown paragraphs."""
        paragraphs = []
        current_block = []
        
        # Heuristic: Group lines that look like they belong together
        for line in self.text_content:
            if len(line) < 50 and not line.endswith('.'):
                # Likely a header or title line
                if current_block:
                    paragraphs.append(" ".join(current_block))
                    current_block = []
                paragraphs.append(f"\n## {line}\n")
            else:
                current_block.append(line)
        
        if current_block:
            paragraphs.append(" ".join(current_block))
            
        return "\n\n".join(paragraphs)


# --- Core Scraper Logic ---

class RecursiveScraper:
    def __init__(self, max_depth: int, links_per_page: int, output_file: str):
        self.max_depth = max_depth
        self.links_per_page = links_per_page
        self.output_file = output_file
        
        self.visited_urls: Set[str] = set()
        self.rp = urllib.robotparser.RobotFileParser()
        
        # Load API config if available
        self.api_key = os.getenv("SCRAPER_API_KEY")
        self.api_url = os.getenv("SCRAPER_API_URL")
        self.use_api = bool(self.api_key and self.api_url)

    def _get_headers(self) -> Dict[str, str]:
        return {
            'User-Agent': random.choice(DEFAULT_USER_AGENTS),
            'Accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8',
            'Accept-Language': 'en-US,en;q=0.9',
            'Accept-Encoding': 'gzip, deflate',
            'Connection': 'keep-alive',
        }

    def _check_robots(self, url: str) -> bool:
        """Checks robots.txt before fetching. Returns True if allowed."""
        try:
            parsed = urllib.parse.urlparse(url)
            robots_url = f"{parsed.scheme}://{parsed.netloc}/robots.txt"
            self.rp.set_url(robots_url)
            self.rp.read()
            return self.rp.can_fetch(self._get_headers()['User-Agent'], url)
        except Exception as e:
            logger.warning(f"Could not check robots.txt for {url}: {e}. Proceeding anyway.")
            return True

    def _fetch_content(self, url: str) -> str:
        """Fetches HTML content using stdlib or external API."""
        
        # 1. Try External API if configured (Graceful Degradation)
        if self.use_api:
            try:
                logger.info(f"Attempting External API fetch for {url}")
                # Construct API request (Generic pattern for reader APIs)
                req_url = f"{self.api_url.rstrip('/')}/{url}"
                req = urllib.request.Request(req_url, headers={'Authorization': f'Bearer {self.api_key}'})
                with urllib.request.urlopen(req, timeout=15) as response:
                    content = response.read().decode('utf-8')
                    # Assume API returns cleaned text or JSON. Assuming raw text/markdown for simplicity here.
                    return content
            except Exception as e:
                logger.warning(f"External API failed ({e}). Falling back to raw parsing.")

        # 2. Fallback to Standard Urllib Fetch
        if not self._check_robots(url):
            raise PermissionsError(f"Blocked by robots.txt: {url}")

        try:
            req = urllib.request.Request(url, headers=self._get_headers())
            with urllib.request.urlopen(req, timeout=10) as response:
                # Handle charset if available in headers
                charset = response.headers.get_content_charset() or 'utf-8'
                return response.read().decode(charset, errors='replace')
        except urllib.error.HTTPError as e:
            raise NetworkError(f"HTTP Error {e.code} for {url}")
        except urllib.error.URLError as e:
            raise NetworkError(f"URL Error {e.reason} for {url}")
        except Exception as e:
            raise ScraperError(f"Unexpected error fetching {url}: {e}")

    def _process_links(self, raw_links: List[Tuple[str, str]], base_domain: str) -> List[str]:
        """
        Scores and ranks links.
        Logic:
        1. Filter: Same domain preferred (usually relevant context).
        2. Filter: Avoid images/files.
        3. Score: Longer anchor text = better context.
        """
        scored_links = []
        
        for url, anchor in raw_links:
            # Normalize URL
            parsed = urllib.parse.urlparse(url)
            if parsed.query: # Strip UTM/Tracking parameters lightly
                clean_url = f"{parsed.scheme}://{parsed.netloc}{parsed.path}"
            else:
                clean_url = url

            # Basic filtering
            if clean_url in self.visited_urls:
                continue
            if clean_url.endswith(('.png', '.jpg', '.gif', '.pdf', '.zip', '.xml')):
                continue
            
            # Scoring
            score = len(anchor)
            # Bonus for same domain
            if parsed.netloc == base_domain:
                score += 20
            
            scored_links.append((score, clean_url))

        # Sort by score descending
        scored_links.sort(key=lambda x: x[0], reverse=True)
        
        # Return only URLs, limited by config
        return [url for score, url in scored_links[:self.links_per_page]]

    def scrape(self, url: str, depth: int = 0) -> str:
        if depth > self.max_depth:
            return ""
        
        if url in self.visited_urls:
            return ""
        
        self.visited_urls.add(url)
        parsed_base = urllib.parse.urlparse(url)
        base_domain = parsed_base.netloc

        logger.info(f"{'  '*depth}Scraping [{depth}/{self.max_depth}]: {url}")
        
        try:
            html_content = self._fetch_content(url)
            
            # Parse Logic
            if self.use_api and "API failed" not in str(html_content):
                # If API was used, content might already be markdown. 
                # Minimal processing needed, just formatting.
                body_text = html_content
                extracted_links = [] # API readers usually don't return links easily without JSON parsing
            else:
                # Local Parsing
                parser = ContentExtractor(url)
                parser.feed(html_content)
                body_text = parser.get_markdown()
                extracted_links = parser.links

            # Format Output
            output_section = f"\n\n# Source: {url}\n\n"
            output_section += body_text
            output_section += "\n\n---\n"

            # Recursive Step
            if depth < self.max_depth:
                top_links = self._process_links(extracted_links, base_domain)
                
                for next_url in top_links:
                    try:
                        output_section += self.scrape(next_url, depth + 1)
                        # Be polite
                        time.sleep(1)
                    except ScraperError as e:
                        logger.warning(f"{'  '*(depth+1)}Skipping {next_url}: {e}")
                        continue

            return output_section

        except ScraperError as e:
            logger.error(f"Failed to scrape {url}: {e}")
            return f"\n\n# Error: {url}\n\nCould not retrieve content: {e}\n\n---\n"

# --- CLI Entry Point ---

def main():
    parser = argparse.ArgumentParser(
        description="Recursive CLI scraper generating LLM-ready research dumps.",
        formatter_class=argparse.RawTextHelpFormatter,
        epilog="Example: depth-scrape https://example.com --depth 2 --limit 5"
    )
    
    parser.add_argument("url", help="The root URL to start scraping from.")
    parser.add_argument(
        "--depth", 
        type=int, 
        default=1, 
        help="Recursion depth (how many hops deep from source). Default: 1."
    )
    parser.add_argument(
        "--limit", 
        type=int, 
        default=3, 
        help="Number of top links to follow per page. Default: 3."
    )
    parser.add_argument(
        "--output", 
        type=str, 
        default="research_dump.md",
        help="Output filename. Default: research_dump.md"
    )

    args = parser.parse_args()

    # Input Validation
    if not args.url.startswith(('http://', 'https://')):
        logger.error("URL must start with http:// or https://")
        sys.exit(1)

    if args.depth < 0:
        logger.error("Depth cannot be negative.")
        sys.exit(1)

    try:
        logger.info(f"Starting Neon Harbor Scraper: {args.url}")
        scraper = RecursiveScraper(
            max_depth=args.depth,
            links_per_page=args.limit,
            output_file=args.output
        )
        
        aggregated_content = scraper.scrape(args.url)
        
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write("# Research Dump\n")
            f.write(f"Source Root: {args.url}\n")
            f.write(f"Depth: {args.depth} | Links per page: {args.limit}\n")
            f.write("=" * 50 + "\n")
            f.write(aggregated_content)
            
        logger.info(f"Success. Data written to {args.output}")
        
    except KeyboardInterrupt:
        logger.warning("\nProcess interrupted by user.")
        sys.exit(130)
    except Exception as e:
        logger.critical(f"Fatal error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()