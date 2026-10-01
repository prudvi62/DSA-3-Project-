/**
 * ==========================================================================
 * SCRIPT.JS
 * Project: Repeated Substring Detection in Large Documents Using Suffix Structures
 * Course: Data Structures and Algorithms - 3 (25CS2103E)
 * Academic Year: 2026-2027 | Section: 5
 * 
 * Team Members:
 *  - KUDUMULA ASHISH IGNATIUS
 *  - NARAYANAGARI PRUDVIRAJ GOUD
 *  - KOLASANI NAVADEEP
 * 
 * Guide: D. SWATHI, Assistant Professor, CSE
 * ==========================================================================
 */

// Sample Data Library
const SAMPLE_TEXTS = {
  academic: `In computer science and bioinformatics, repeated substring detection is a fundamental problem with wide applications in text compression, data deduplication, plagiarism detection, and genome sequence analysis. 

A suffix array is a sorted array of all suffixes of a string. Suffix arrays were introduced by Udi Manber and Gene Myers in 1990 as a space-efficient alternative to suffix trees. When combined with the Longest Common Prefix (LCP) array, suffix structures allow efficient identification of repeated patterns in large documents.

The Longest Common Prefix (LCP) array stores the length of the common prefix between adjacent suffixes in the sorted suffix array. Kasai's algorithm computes the LCP array in linear O(n) time. By inspecting high LCP values, one can quickly extract repeated substrings and determine the longest repeated substring without performing expensive pairwise substring comparisons.

In contrast, a naive substring-search method compares substrings across all possible starting positions and lengths. The naive approach incurs a time complexity of O(n^2) to O(n^3), which becomes prohibitively slow as the text document grows. The suffix array and LCP approach achieves O(n log n) or O(n) construction and rapid querying, providing substantial performance improvements for large document analysis.

Therefore, suffix arrays and Longest Common Prefix arrays remain essential data structures in modern algorithm design.`,

  dna: `ATGCGATCGATCGATCGTAAATCGATCGATCGATCGTTAGGCTATCGATCGAATGCGATCGATCGATCGTAAAGCTAGCTAGCTAGCTAATGCGATCGATCGATCGAATCGATCGATCGATCGTTAGGCTATCGATCGAAGCTAGCTAGCTAGCTA`,

  literature: `It was the best of times, it was the worst of times, it was the age of wisdom, it was the age of foolishness, it was the epoch of belief, it was the epoch of incredulity, it was the season of light, it was the season of darkness, it was the spring of hope, it was the winter of despair.`
};

// Global State
let currentAnalysis = {
  text: "",
  sa: null,
  lcp: null,
  repeatedSubstrings: [],
  longestRepeatedSubstring: null,
  saTimeMs: 0,
  naiveTimeMs: 0,
  naiveResultsCount: 0
};

// ==========================================================================
// 1. SUFFIX ARRAY CONSTRUCTION
// Prefix Doubling (Manber-Myers style) - O(n log^2 n)
// ==========================================================================
/**
 * Builds the Suffix Array for the given text.
 * Stores the starting indices of all suffixes in lexicographically sorted order.
 * @param {string} text - The input document string.
 * @returns {Int32Array} - Suffix array of starting indices.
 */
function buildSuffixArray(text) {
  const n = text.length;
  if (n === 0) return new Int32Array(0);

  const sa = new Int32Array(n);
  const rank = new Int32Array(n);
  const tempRank = new Int32Array(n);

  // Initial rank based on initial character code
  for (let i = 0; i < n; i++) {
    sa[i] = i;
    rank[i] = text.charCodeAt(i);
  }

  // Prefix doubling: sort by prefix of length 2^k
  for (let k = 1; k < n; k *= 2) {
    // Sort comparator based on pair: (rank[i], rank[i + k])
    sa.sort((a, b) => {
      if (rank[a] !== rank[b]) {
        return rank[a] - rank[b];
      }
      const rankA_k = a + k < n ? rank[a + k] : -1;
      const rankB_k = b + k < n ? rank[b + k] : -1;
      return rankA_k - rankB_k;
    });

    // Recompute ranks for next iteration
    tempRank[sa[0]] = 0;
    for (let i = 1; i < n; i++) {
      const prev = sa[i - 1];
      const curr = sa[i];
      const prevK = prev + k < n ? rank[prev + k] : -1;
      const currK = curr + k < n ? rank[curr + k] : -1;

      if (rank[curr] === rank[prev] && currK === prevK) {
        tempRank[curr] = tempRank[prev];
      } else {
        tempRank[curr] = tempRank[prev] + 1;
      }
    }

    for (let i = 0; i < n; i++) {
      rank[i] = tempRank[i];
    }

    // Early termination if all ranks are unique
    if (rank[sa[n - 1]] === n - 1) {
      break;
    }
  }

  return sa;
}

// ==========================================================================
// 2. LONGEST COMMON PREFIX (LCP) ARRAY CONSTRUCTION
// Kasai's Algorithm - Guaranteed Linear O(n)
// ==========================================================================
/**
 * Builds the LCP Array using Kasai's Algorithm in O(n) time.
 * lcp[i] represents the length of the longest common prefix between
 * suffix sa[i - 1] and suffix sa[i].
 * @param {string} text - The input document string.
 * @param {Int32Array} sa - The suffix array.
 * @returns {Int32Array} - LCP array where lcp[0] = 0.
 */
function buildLCPArray(text, sa) {
  const n = text.length;
  if (n === 0) return new Int32Array(0);

  const lcp = new Int32Array(n);
  const rank = new Int32Array(n);

  // Invert suffix array: rank[i] is index in SA where suffix i begins
  for (let i = 0; i < n; i++) {
    rank[sa[i]] = i;
  }

  let h = 0; // Length of current common prefix
  for (let i = 0; i < n; i++) {
    if (rank[i] > 0) {
      const j = sa[rank[i] - 1]; // Preceding suffix in suffix array
      while (i + h < n && j + h < n && text[i + h] === text[j + h]) {
        h++;
      }
      lcp[rank[i]] = h;
      if (h > 0) {
        h--;
      }
    } else {
      lcp[0] = 0;
    }
  }

  return lcp;
}

// ==========================================================================
// 3. CALCULATE POSITIONS AND OCCURRENCES
// Exact match search to retrieve 0-indexed positions
// ==========================================================================
/**
 * Finds all exact starting positions of pattern in text.
 * @param {string} text - Document string.
 * @param {string} pattern - Substring pattern to locate.
 * @returns {number[]} - Array of starting index positions.
 */
function calculatePositions(text, pattern) {
  if (!pattern || pattern.length === 0) return [];
  const positions = [];
  let idx = text.indexOf(pattern, 0);
  while (idx !== -1) {
    positions.push(idx);
    idx = text.indexOf(pattern, idx + 1);
  }
  return positions;
}

// ==========================================================================
// 4. FIND REPEATED SUBSTRINGS USING SA & LCP
// ==========================================================================
/**
 * Detects distinct repeated substrings using Suffix Array and LCP values.
 * Identifies maximal patterns with length >= minLen and records occurrences and positions.
 * @param {string} text - Input text document.
 * @param {Int32Array} sa - Suffix array.
 * @param {Int32Array} lcp - LCP array.
 * @param {number} minLen - Minimum substring length filter.
 * @param {number} maxResults - Maximum number of results to return.
 * @param {boolean} maximalOnly - If true, filters out non-maximal sub-patterns sharing identical occurrences.
 * @returns {Object} - List of repeated substrings and the Longest Repeated Substring.
 */
function findRepeatedSubstrings(text, sa, lcp, minLen = 3, maxResults = 50, maximalOnly = true) {
  const n = text.length;
  const rawCandidates = new Map();
  let longestRepeated = null;
  let maxLcpVal = 0;

  // Scan the LCP array: every lcp[i] >= minLen indicates an adjacent common prefix
  for (let i = 1; i < n; i++) {
    const lcpLen = lcp[i];
    if (lcpLen >= minLen) {
      const sub = text.substring(sa[i], sa[i] + lcpLen);

      if (!rawCandidates.has(sub)) {
        const positions = calculatePositions(text, sub);
        if (positions.length >= 2) {
          const item = {
            substring: sub,
            length: sub.length,
            occurrences: positions.length,
            positions: positions
          };
          rawCandidates.set(sub, item);

          if (sub.length > maxLcpVal) {
            maxLcpVal = sub.length;
            longestRepeated = item;
          }
        }
      }

      // Also extract clean trimmed words / phrases if multi-word
      const trimmed = sub.trim();
      if (trimmed.length >= minLen && trimmed !== sub && !rawCandidates.has(trimmed)) {
        const tPositions = calculatePositions(text, trimmed);
        if (tPositions.length >= 2) {
          rawCandidates.set(trimmed, {
            substring: trimmed,
            length: trimmed.length,
            occurrences: tPositions.length,
            positions: tPositions
          });
        }
      }
    }
  }

  let candidates = Array.from(rawCandidates.values());

  // Maximal Substring Filtering:
  // If candidate B is a substring of candidate A, has the exact same occurrences count,
  // AND occurs at the exact same relative offset in all occurrences, candidate B is redundant.
  if (maximalOnly && candidates.length > 1) {
    // Sort descending by length first
    candidates.sort((a, b) => b.length - a.length);

    const filtered = [];
    for (let i = 0; i < candidates.length; i++) {
      const curr = candidates[i];
      let isRedundant = false;

      for (let j = 0; j < filtered.length; j++) {
        const parent = filtered[j];
        if (parent.length > curr.length && parent.occurrences === curr.occurrences) {
          const offset = parent.substring.indexOf(curr.substring);
          if (offset !== -1) {
            // Verify every position matches parent.positions[k] + offset
            let allMatch = true;
            for (let k = 0; k < curr.positions.length; k++) {
              if (curr.positions[k] !== parent.positions[k] + offset) {
                allMatch = false;
                break;
              }
            }
            if (allMatch) {
              isRedundant = true;
              break;
            }
          }
        }
      }

      if (!isRedundant) {
        filtered.push(curr);
      }
    }
    candidates = filtered;
  }

  // Sort primarily by length descending, then occurrences descending
  candidates.sort((a, b) => {
    if (b.length !== a.length) {
      return b.length - a.length;
    }
    return b.occurrences - a.occurrences;
  });

  return {
    repeatedSubstrings: candidates.slice(0, maxResults),
    totalFound: candidates.length,
    longestRepeatedSubstring: longestRepeated || (candidates.length > 0 ? candidates[0] : null)
  };
}

// ==========================================================================
// 5. NAÏVE REPEATED SUBSTRING SEARCH (FOR PERFORMANCE BENCHMARK)
// Performs direct pairwise / sliding window search
// ==========================================================================
/**
 * Naive baseline method for finding repeated substrings without suffix structures.
 * Checks substrings iteratively and uses text.indexOf() to test for recurrence.
 * @param {string} text - Input text document.
 * @param {number} minLen - Minimum substring length.
 * @param {number} maxResults - Max items to find.
 * @returns {Array} - Array of found repeated substrings.
 */
function naiveRepeatedSubstringSearch(text, minLen = 3, maxResults = 50) {
  const n = text.length;
  const foundMap = new Map();
  
  // Guard for extreme sizes to prevent total UI freeze during presentation
  const searchLimit = Math.min(n, 2500);

  // Naive nested loops: check lengths from minLen upwards
  for (let len = minLen; len <= Math.min(100, searchLimit); len++) {
    for (let i = 0; i <= searchLimit - len; i++) {
      const candidate = text.substring(i, i + len);

      if (!foundMap.has(candidate)) {
        // Check if this candidate appears anywhere after i
        const nextPos = text.indexOf(candidate, i + 1);
        if (nextPos !== -1) {
          const positions = calculatePositions(text, candidate);
          foundMap.set(candidate, {
            substring: candidate,
            length: candidate.length,
            occurrences: positions.length,
            positions: positions
          });

          if (foundMap.size >= maxResults) {
            return Array.from(foundMap.values());
          }
        }
      }
    }
  }

  return Array.from(foundMap.values());
}

// ==========================================================================
// 6. MAIN DOCUMENT ANALYZER FUNCTION
// Coordinates parsing, timing, algorithm execution, and UI dispatch
// ==========================================================================
function analyzeDocument() {
  const textInput = document.getElementById("documentInput");
  const minLenInput = document.getElementById("minSubstringLen");
  const maxResultsInput = document.getElementById("maxResults");
  const statusBanner = document.getElementById("statusBanner");

  const text = textInput.value;
  const minLen = parseInt(minLenInput.value, 10);
  const maxResults = parseInt(maxResultsInput.value, 10);
  const maximalCheckbox = document.getElementById("maximalOnlyCheck");
  const maximalOnly = maximalCheckbox ? maximalCheckbox.checked : true;

  // Validation
  if (!text || text.trim().length === 0) {
    showStatus("Please enter or paste document text before running analysis.", "error");
    return;
  }

  if (isNaN(minLen) || minLen < 1) {
    showStatus("Minimum substring length must be a positive integer (>= 1).", "error");
    return;
  }

  if (minLen > text.length) {
    showStatus(`Minimum substring length (${minLen}) cannot exceed document length (${text.length}).`, "error");
    return;
  }

  hideStatus();

  // Disable analyze button briefly while computing
  const analyzeBtn = document.getElementById("analyzeBtn");
  const originalBtnText = analyzeBtn.innerHTML;
  analyzeBtn.disabled = true;
  analyzeBtn.innerHTML = `<span>Processing Algorithms...</span>`;

  // Use setTimeout to allow UI to render status/loader smoothly
  setTimeout(() => {
    try {
      // 1. Measure Suffix Array + LCP Construction and Detection
      const t0 = performance.now();
      const sa = buildSuffixArray(text);
      const lcp = buildLCPArray(text, sa);
      const detectionResult = findRepeatedSubstrings(text, sa, lcp, minLen, maxResults, maximalOnly);
      const t1 = performance.now();
      const saTimeMs = Math.max(0.01, t1 - t0);

      // 2. Measure Naive Method
      const t2 = performance.now();
      const naiveResults = naiveRepeatedSubstringSearch(text, minLen, maxResults);
      const t3 = performance.now();
      const naiveTimeMs = Math.max(0.01, t3 - t2);

      // Store in global state
      currentAnalysis = {
        text: text,
        sa: sa,
        lcp: lcp,
        repeatedSubstrings: detectionResult.repeatedSubstrings,
        totalFound: detectionResult.totalFound,
        longestRepeatedSubstring: detectionResult.longestRepeatedSubstring,
        saTimeMs: saTimeMs,
        naiveTimeMs: naiveTimeMs,
        naiveResultsCount: naiveResults.length
      };

      // Display all output sections
      displayResults();
      displayLCPVisualization();
      comparePerformance();

      // Show dashboard
      document.getElementById("resultsDashboard").style.display = "block";
      document.getElementById("lrsSection").style.display = "block";
      document.getElementById("lcpSection").style.display = "block";
      document.getElementById("performanceSection").style.display = "block";

      // Scroll smoothly to results
      document.getElementById("resultsDashboard").scrollIntoView({ behavior: "smooth" });

      showStatus(`Analysis complete! Identified ${detectionResult.totalFound} repeated substring pattern(s).`, "success");
    } catch (err) {
      console.error("Analysis Error:", err);
      showStatus("An error occurred during analysis: " + err.message, "error");
    } finally {
      analyzeBtn.disabled = false;
      analyzeBtn.innerHTML = originalBtnText;
    }
  }, 20);
}

// ==========================================================================
// 7. DISPLAY RESULTS (DASHBOARD & TABLE)
// ==========================================================================
function displayResults() {
  const { text, sa, repeatedSubstrings, totalFound, longestRepeatedSubstring, saTimeMs } = currentAnalysis;

  // 1. Summary Cards
  document.getElementById("metricTotalChars").textContent = text.length.toLocaleString();
  document.getElementById("metricTotalSuffixes").textContent = sa.length.toLocaleString();
  document.getElementById("metricRepeatedFound").textContent = totalFound.toLocaleString();

  if (longestRepeatedSubstring) {
    document.getElementById("metricLRS").textContent = `"${longestRepeatedSubstring.substring.slice(0, 18)}${longestRepeatedSubstring.substring.length > 18 ? '...' : ''}"`;
    document.getElementById("metricTotalOccurrences").textContent = longestRepeatedSubstring.occurrences.toLocaleString();
  } else {
    document.getElementById("metricLRS").textContent = "None";
    document.getElementById("metricTotalOccurrences").textContent = "0";
  }

  document.getElementById("metricExecutionTime").textContent = `${saTimeMs.toFixed(2)} ms`;

  // 2. Longest Repeated Substring Highlight Card
  const lrsContainer = document.getElementById("lrsDetailsContent");
  if (longestRepeatedSubstring) {
    lrsContainer.innerHTML = `
      <div class="lrs-header">
        <div class="lrs-tag">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M12 2l3.09 6.26L22 9.27l-5 4.87 1.18 6.88L12 17.77l-6.18 3.25L7 14.14 2 9.27l6.91-1.01L12 2z"/></svg>
          Maximal Repeated Pattern
        </div>
        <span class="badge badge-count">${longestRepeatedSubstring.occurrences} occurrences</span>
      </div>
      <div class="lrs-content-wrapper">
        <div class="lrs-text">"${escapeHtml(longestRepeatedSubstring.substring)}"</div>
      </div>
      <div class="lrs-metrics-grid">
        <div class="lrs-metric-item">
          <div class="lrs-metric-label">Pattern Length</div>
          <div class="lrs-metric-val">${longestRepeatedSubstring.length} characters</div>
        </div>
        <div class="lrs-metric-item">
          <div class="lrs-metric-label">Total Occurrences</div>
          <div class="lrs-metric-val">${longestRepeatedSubstring.occurrences} times</div>
        </div>
        <div class="lrs-metric-item">
          <div class="lrs-metric-label">Document Starting Positions (0-indexed)</div>
          <div class="lrs-metric-positions mono">${longestRepeatedSubstring.positions.join(", ")}</div>
        </div>
      </div>
    `;
  } else {
    lrsContainer.innerHTML = `
      <div class="empty-state">
        <div class="empty-icon">🔍</div>
        <p>No repeated substring found for the selected minimum length.</p>
      </div>
    `;
  }

  // 3. Repeated Substrings Data Table
  renderSubstringsTable(repeatedSubstrings);
}

/**
 * Helper to render or filter the repeated substrings table
 */
function renderSubstringsTable(substrings) {
  const tbody = document.getElementById("substringsTableBody");
  const countBadge = document.getElementById("tableResultsCountBadge");
  tbody.innerHTML = "";

  if (countBadge) {
    countBadge.textContent = `${substrings.length} shown`;
  }

  if (substrings.length === 0) {
    tbody.innerHTML = `
      <tr>
        <td colspan="4" class="empty-state" style="padding: 2rem;">
          No repeated patterns match current criteria or filter.
        </td>
      </tr>
    `;
    return;
  }

  substrings.forEach((item) => {
    const tr = document.createElement("tr");

    const positionsText = item.positions.join(", ");

    tr.innerHTML = `
      <td class="substring-cell">
        <span title="${escapeHtml(item.substring)}">"${escapeHtml(item.substring)}"</span>
      </td>
      <td>
        <span class="badge badge-len">${item.length}</span>
      </td>
      <td>
        <span class="badge badge-count">${item.occurrences}</span>
      </td>
      <td class="positions-cell" title="Positions: ${positionsText}">
        ${positionsText}
      </td>
    `;
    tbody.appendChild(tr);
  });
}

// ==========================================================================
// 8. LCP VISUALIZATION
// Displays Suffix Array rank, position, preview, and Kasai's LCP value
// ==========================================================================
function displayLCPVisualization() {
  const { text, sa, lcp } = currentAnalysis;
  const tbody = document.getElementById("lcpTableBody");
  tbody.innerHTML = "";

  const n = sa.length;
  // Display up to 50 suffixes for clean readability
  const displayLimit = Math.min(n, 50);

  // Find max LCP for proportional visual bar
  let maxLcp = 1;
  for (let i = 0; i < n; i++) {
    if (lcp[i] > maxLcp) maxLcp = lcp[i];
  }

  for (let i = 0; i < displayLimit; i++) {
    const pos = sa[i];
    const rawPreview = text.substring(pos, pos + 40);
    const cleanPreview = rawPreview.replace(/\n/g, "↵ ");
    const lcpVal = lcp[i];
    const barWidth = Math.max(4, Math.round((lcpVal / maxLcp) * 100));

    const tr = document.createElement("tr");
    tr.innerHTML = `
      <td class="mono" style="color: var(--text-muted); font-size: 0.8rem;">${i}</td>
      <td class="mono" style="font-weight: 600; color: var(--text-accent);">${pos}</td>
      <td class="mono" style="font-size: 0.85rem; color: var(--text-primary); max-width: 320px; word-break: break-all;">
        "${escapeHtml(cleanPreview)}${text.length - pos > 40 ? '...' : ''}"
      </td>
      <td>
        <div class="lcp-cell-bar-container">
          <span class="badge badge-lcp">${lcpVal}</span>
          ${lcpVal > 0 ? `<div class="lcp-cell-bar" style="width: ${barWidth}px;"></div>` : ''}
        </div>
      </td>
    `;
    tbody.appendChild(tr);
  }

  const lcpFootnote = document.getElementById("lcpFootnote");
  if (n > displayLimit) {
    lcpFootnote.textContent = `Showing first ${displayLimit} of ${n} sorted suffixes in the suffix array.`;
  } else {
    lcpFootnote.textContent = `Showing all ${n} sorted suffixes and their Longest Common Prefix values.`;
  }
}

// ==========================================================================
// 9. PERFORMANCE COMPARISON & VISUAL CHART
// ==========================================================================
function comparePerformance() {
  const { saTimeMs, naiveTimeMs, totalFound, naiveResultsCount } = currentAnalysis;

  // Update table cells
  document.getElementById("saTimeCell").textContent = `${saTimeMs.toFixed(2)} ms`;
  document.getElementById("saResultsCell").textContent = totalFound.toLocaleString();

  document.getElementById("naiveTimeCell").textContent = `${naiveTimeMs.toFixed(2)} ms`;
  document.getElementById("naiveResultsCell").textContent = naiveResultsCount.toLocaleString();

  // Speedup multiplier
  const speedup = (naiveTimeMs / Math.max(saTimeMs, 0.01)).toFixed(1);
  const speedupBadge = document.getElementById("speedupBadge");
  if (speedup > 1.0) {
    speedupBadge.textContent = `${speedup}x Faster`;
    speedupBadge.style.display = "inline-block";
  } else {
    speedupBadge.textContent = `Comparable`;
    speedupBadge.style.display = "inline-block";
  }

  // Visual Bar Chart Widths
  const maxTime = Math.max(saTimeMs, naiveTimeMs, 0.01);
  const saPct = Math.max(6, Math.round((saTimeMs / maxTime) * 100));
  const naivePct = Math.max(6, Math.round((naiveTimeMs / maxTime) * 100));

  const saBar = document.getElementById("saBarFill");
  const naiveBar = document.getElementById("naiveBarFill");

  saBar.style.width = `${saPct}%`;
  saBar.textContent = `${saTimeMs.toFixed(2)} ms`;

  naiveBar.style.width = `${naivePct}%`;
  naiveBar.textContent = `${naiveTimeMs.toFixed(2)} ms`;
}

// ==========================================================================
// UI HELPER FUNCTIONS & EVENT LISTENERS
// ==========================================================================

function showStatus(message, type = "info") {
  const banner = document.getElementById("statusBanner");
  banner.textContent = message;
  banner.className = `status-banner ${type}`;
}

function hideStatus() {
  const banner = document.getElementById("statusBanner");
  banner.className = "status-banner";
  banner.style.display = "none";
}

function escapeHtml(str) {
  if (!str) return "";
  return str
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#039;");
}

// Initialize on DOMContentLoaded
document.addEventListener("DOMContentLoaded", () => {
  const documentInput = document.getElementById("documentInput");
  const charCounter = document.getElementById("charCounter");
  const tableFilter = document.getElementById("tableFilter");

  // Character counter
  function updateCharCount() {
    charCounter.textContent = `${documentInput.value.length.toLocaleString()} characters`;
  }
  documentInput.addEventListener("input", updateCharCount);

  // Load Initial Sample Text by default so presentation is ready immediately
  loadSample('academic');

  // Filter for Results Table
  tableFilter.addEventListener("input", (e) => {
    const query = e.target.value.toLowerCase().trim();
    if (!currentAnalysis.repeatedSubstrings) return;
    
    if (!query) {
      renderSubstringsTable(currentAnalysis.repeatedSubstrings);
    } else {
      const filtered = currentAnalysis.repeatedSubstrings.filter((item) =>
        item.substring.toLowerCase().includes(query)
      );
      renderSubstringsTable(filtered);
    }
  });

  // Attach button events
  document.getElementById("analyzeBtn").addEventListener("click", analyzeDocument);
  document.getElementById("clearBtn").addEventListener("click", clearDocument);
  
  const exportCsvBtn = document.getElementById("exportCsvBtn");
  if (exportCsvBtn) {
    exportCsvBtn.addEventListener("click", exportTableToCsv);
  }

  // File Upload Handler
  const fileUploadInput = document.getElementById("fileUploadInput");
  if (fileUploadInput) {
    fileUploadInput.addEventListener("change", (e) => {
      const file = e.target.files[0];
      if (!file) return;

      const reader = new FileReader();
      reader.onload = (evt) => {
        documentInput.value = evt.target.result;
        updateCharCount();
        showStatus(`Loaded file "${file.name}" (${file.size.toLocaleString()} bytes). Click "Analyze Document" to process.`, "success");
      };
      reader.onerror = () => {
        showStatus("Failed to read file.", "error");
      };
      reader.readAsText(file);
      fileUploadInput.value = "";
    });
  }
});

/**
 * Exports currently detected repeated substrings to CSV file
 */
function exportTableToCsv() {
  if (!currentAnalysis.repeatedSubstrings || currentAnalysis.repeatedSubstrings.length === 0) {
    showStatus("No analysis results to export.", "error");
    return;
  }

  const rows = [["Repeated Substring", "Length", "Occurrences", "Positions"]];
  currentAnalysis.repeatedSubstrings.forEach((item) => {
    const safeSub = `"${item.substring.replace(/"/g, '""')}"`;
    const safePos = `"${item.positions.join(", ")}"`;
    rows.push([safeSub, item.length, item.occurrences, safePos]);
  });

  const csvContent = "data:text/csv;charset=utf-8," + rows.map(r => r.join(",")).join("\n");
  const encodedUri = encodeURI(csvContent);
  const link = document.createElement("a");
  link.setAttribute("href", encodedUri);
  link.setAttribute("download", "repeated_substrings_analysis.csv");
  document.body.appendChild(link);
  link.click();
  document.body.removeChild(link);
}

// Sample text loader
function loadSample(type = 'academic') {
  const text = SAMPLE_TEXTS[type] || SAMPLE_TEXTS.academic;
  const textInput = document.getElementById("documentInput");
  textInput.value = text;
  document.getElementById("charCounter").textContent = `${text.length.toLocaleString()} characters`;
  hideStatus();
}

// Clear document handler
function clearDocument() {
  document.getElementById("documentInput").value = "";
  document.getElementById("charCounter").textContent = "0 characters";
  
  // Hide result panels
  document.getElementById("resultsDashboard").style.display = "none";
  document.getElementById("lrsSection").style.display = "none";
  document.getElementById("lcpSection").style.display = "none";
  document.getElementById("performanceSection").style.display = "none";
  
  hideStatus();
}
