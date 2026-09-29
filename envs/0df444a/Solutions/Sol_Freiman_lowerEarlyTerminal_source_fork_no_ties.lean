-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_source_fork_no_ties
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:04:22.938133+00:00
-- url     : https://prove2.me/submissions/f1ea9291-1b67-410a-9ba6-e8d68cb1597a

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_fork_ranges
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_range
import Theorems.Thm_Freiman_lowerEarlyTerminal_ratio_append
import Theorems.Thm_Freiman_lowerEarlyTerminal_width_tie_ratios
import Theorems.Thm_Freiman_lowerEarlyTerminal_source_fork_no_ties_from_ranges

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (h2 : ¬ lowerEarlyTerminalTie2 p l) (h3 : ¬ lowerEarlyTerminalTie3 p l) :
    ∀ d ∈ ([1,2] : List ℕ+), LowerEarlyTerminalNoTies (lowerEarlyTerminalForkPair p l true d) := by
  exact lowerEarlyTerminal_source_fork_no_ties_from_ranges lowerEarlyTerminal_fork_ranges
    lowerEarlyTerminal_ratio_range lowerEarlyTerminal_ratio_append lowerEarlyTerminal_width_tie_ratios
    t p hs hd l hn h2 h3
