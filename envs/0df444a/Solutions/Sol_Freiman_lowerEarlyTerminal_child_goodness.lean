-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_child_goodness
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:38.22681+00:00
-- url     : https://prove2.me/submissions/364ec22b-8c27-49a0-8ea5-28aec4960037

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness_regular
import Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness_tie2
import Theorems.Thm_Freiman_lowerEarlyTerminal_tie3_exclusion
import Theorems.Thm_Freiman_lowerEarlyTerminal_width_tie_ratios

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (hw : LowerHistoryWidthLaw)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true) (h : ∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) :
    lowerGood (lowerChild p l) := by
  by_cases h2 : lowerEarlyTerminalTie2 p l
  · exact lowerEarlyTerminal_child_goodness_tie2 t p hs hd l hn h2 hw ho h
  · exact lowerEarlyTerminal_child_goodness_regular t p hs hd l hn h2
      (lowerEarlyTerminal_tie3_exclusion lowerEarlyTerminal_width_tie_ratios t p hs hd l hn) hw ho h
