-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_child_goodness_regular
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:39.321799+00:00
-- url     : https://prove2.me/submissions/93616173-e2e5-47f5-aefc-7942cf7c944c

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_source_fork_no_ties
import Theorems.Thm_Freiman_lowerEarlyTerminal_endpoint_swap_nontie
import Theorems.Thm_Freiman_lowerEarlyTerminal_fork_alignment_from_nonties
import Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness_from_alignment

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (h2 : ¬ lowerEarlyTerminalTie2 p l) (h3 : ¬ lowerEarlyTerminalTie3 p l)
    (hw : LowerHistoryWidthLaw)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true) (h : ∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) :
    lowerGood (lowerChild p l) := by
  exact lowerEarlyTerminal_child_goodness_from_alignment p l hw ho
    (lowerEarlyTerminal_fork_alignment_from_nonties p l hw lowerEarlyTerminal_endpoint_swap_nontie
      (lowerEarlyTerminal_source_fork_no_ties t p hs hd l hn h2 h3)) h
