-- Prove2me | solution 1 for Freiman.lowerHistory_marked_side
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-11T02:25:04.37615+00:00
-- url     : https://prove2.me/submissions/fae053dd-dd13-4705-81e6-0f1f4482a34e

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic

open Freiman

set_option autoImplicit false

theorem solution (h : ℕ → LowerPair) (n row : ℕ) (hrow : row ∈ [1,2,3,4]) (haz : lowerHistoryHazard row (h n)) :
    lowerEnds (lowerSide (lowerPhysicalPath h n) (lowerMarkedPhysical h n row)) [3,1,3,1] := by
  classical
  have hside : lowerSide (lowerPhysicalPath h n) (lowerMarkedPhysical h n row) =
      (if row = 1 ∨ row = 3 then (lowerNormalize (h n)).1 else (lowerNormalize (h n)).2) := by
    by_cases hw : lowerWidth (h n).2 ≤ lowerWidth (h n).1
    · have hn : ¬ lowerWidth (h n).1 < lowerWidth (h n).2 := not_lt.mpr hw
      cases ho : lowerOrientation h n <;> by_cases hr : row = 1 ∨ row = 3 <;>
        simp [lowerSide, lowerPhysicalPath, lowerMarkedPhysical, lowerReflects,
          lowerNormalize, hw, hn, ho, hr]
    · have hl : lowerWidth (h n).1 < lowerWidth (h n).2 := lt_of_not_ge hw
      cases ho : lowerOrientation h n <;> by_cases hr : row = 1 ∨ row = 3 <;>
        simp [lowerSide, lowerPhysicalPath, lowerMarkedPhysical, lowerReflects,
          lowerNormalize, hw, hl, ho, hr]
  rw [hside]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
  rcases hrow with rfl | rfl | rfl | rfl
  · simpa [lowerLStar] using (show lowerLStar (h n) from haz.2.2.2)
  · simpa [lowerRStar] using (show lowerRStar (h n) from haz.2.2)
  · simpa [lowerLStar] using (show lowerLStar (h n) from haz.2.2.2)
  · simpa [lowerRStar] using (show lowerRStar (h n) from haz.2.2.2)

#print axioms solution
