-- Prove2me | solution 1 for Freiman.lowerEarlyTerminal_child_goodness_tie2
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:05:38.772784+00:00
-- url     : https://prove2.me/submissions/23678849-d9e5-4b17-8d82-578ea3fe89e1

import Definitions.Def_Freiman_lowerEarlyTerminalGeometry


import Theorems.Thm_Freiman_lowerEarlyTerminal_tie2_relaxation
import Theorems.Thm_Freiman_lowerEarlyTerminal_child_goodness_from_fork_covers

open Freiman

theorem solution (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hd : lowerEarlyDomain p)
    (l : LowerLabel) (hn : lowerEarlyTerminalNative p l)
    (he : lowerEarlyTerminalTie2 p l) (hw : LowerHistoryWidthLaw)
    (ho : ∀ w : LowerPair, lowerEndpoint w false ≤ lowerEndpoint w true) (h : ∀ req ∈ lowerEarlyTerminalGoodRequirements [] l, lowerEarlyTerminalAt p req.1 →
      lowerEarlyTerminalKindHolds p req.2) :
    lowerGood (lowerChild p l) := by
  obtain ⟨norm,hm,ha,hc⟩ := lowerEarlyTerminal_tie2_relaxation t p hs hd l hn he hw
  exact lowerEarlyTerminal_child_goodness_from_fork_covers p l true norm hm ha ho hc h
