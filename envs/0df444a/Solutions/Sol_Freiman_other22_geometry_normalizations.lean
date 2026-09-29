-- Prove2me | solution 1 for Freiman.other22_geometry_normalizations
-- status  : ACCEPTED   (prove)
-- author  : @Koki Yamada
-- created : 2026-09-15T19:50:23.660986+00:00
-- url     : https://prove2.me/submissions/b3bd39f7-883a-4aad-8a3a-4f85e2898e59

import Definitions.Def_Freiman_other22Verification
import Theorems.Thm_Freiman_lowerHistory_width_threshold
import Mathlib.Tactic

open Freiman

private theorem normalized_width (p : LowerPair) (hp : lowerNormalize p = p) :
    lowerWidth p.2 ≤ lowerWidth p.1 := by
  have hn : lowerWidth (lowerNormalize p).2 ≤ lowerWidth (lowerNormalize p).1 := by
    unfold lowerNormalize
    split_ifs with h
    · exact h
    · exact le_of_not_ge h
  simpa only [hp] using hn

theorem solution (Z B R S : LowerPair) (h : LowerOther22Geometry Z B R S)
    (k : Fin 6) (hc : lowerHistoryContextFits Z (other22Context k)) :
    lowerHistoryNormalizationEvents Z (other22Paths k) := by
  have hB : B = (Z.1 ++ [2], Z.2 ++ [3]) := by
    rw [h.birth]
    simp [lowerChild, h.normalizedZ]
  have hR : R = (Z.1 ++ [2, 2], Z.2 ++ [3]) := by
    rw [h.stepR]
    simp only [lowerChild, h.normalizedB]
    simp [hB, List.append_assoc]
  have hS : S = (Z.2 ++ [3, 1], Z.1 ++ [2, 2]) := by
    rw [h.stepS]
    simp [lowerChild, h.normalizedR, hB, List.append_assoc]
  have hBwidth : lowerWidth (Z.2 ++ [3]) ≤ lowerWidth (Z.1 ++ [2]) := by
    simpa only [hB] using normalized_width B h.normalizedB
  have hRwidth : lowerWidth (Z.1 ++ [2, 2]) < lowerWidth (Z.2 ++ [3]) := by
    simpa only [hR] using h.reflectsR
  have hSwidth : lowerWidth (Z.1 ++ [2, 2]) ≤ lowerWidth (Z.2 ++ [3, 1]) := by
    simpa only [hS] using normalized_width S h.normalizedS
  have hBcert : lowerHistoryAtBase Z
      [⟨false, false, lowerHistoryWH ([2], [3])⟩] :=
    (lowerHistory_width_threshold Z ([2], [3])).1.mp hBwidth
  have hRnot : ¬ lowerHistoryAtBase Z
      [⟨false, false, lowerHistoryWH ([2, 2], [3])⟩] := by
    intro hc
    exact (not_le_of_gt hRwidth)
      ((lowerHistory_width_threshold Z ([2, 2], [3])).1.mpr hc)
  have hRcert : lowerHistoryAtBase Z
      [⟨true, true, lowerHistoryWH ([2, 2], [3])⟩] := by
    simpa [lowerHistoryAtBase, lowerHistoryConditions, certBoundHolds] using hRnot
  have hSnot : ¬ lowerHistoryAtBase Z
      [⟨false, true, lowerHistoryWH ([2, 2], [3, 1])⟩] := by
    intro hc
    exact (not_lt_of_ge hSwidth)
      ((lowerHistory_width_threshold Z ([2, 2], [3, 1])).2.mpr hc)
  have hScert : lowerHistoryAtBase Z
      [⟨true, false, lowerHistoryWH ([2, 2], [3, 1])⟩] := by
    simpa [lowerHistoryAtBase, lowerHistoryConditions, certBoundHolds] using hSnot
  fin_cases k <;> intro j hj <;> change j ≤ 2 at hj
  all_goals interval_cases j
  all_goals first | exact hBcert | exact hRcert | exact hScert
