-- Prove2me | solution 1 for Freiman.lower_h5_marked_priority
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-13T08:44:28.399136+00:00
-- url     : https://prove2.me/submissions/5d0f1f65-352f-459d-9529-780673ad715a

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

theorem solution (p : LowerPair) (t : ℝ)
    (hl : lowerLocalLower p ([2],[2]) ≤ lowerLocalCoordinate p t)
    (hp : t ∉ lowerCover (lowerChild p ([2],[2]))) :
    lowerH5LocalUpper p ([2],[2]) < lowerLocalCoordinate p t := by
  unfold lowerLocalLower lowerLocalCoordinate at hl
  unfold lowerH5LocalUpper lowerLocalCoordinate
  unfold lowerCover at hp
  simp only [Set.mem_Icc] at hp
  by_cases he : (lowerNormalize p).1.length % 2 = 0
  · simp only [if_pos he] at hl ⊢
    by_contra h
    exact hp ⟨hl, le_of_not_gt h⟩
  · simp only [if_neg he] at hl ⊢
    have hut : t ≤ lowerEndpoint (lowerChild p ([2], [2])) true := by linarith
    have hlt : t < lowerEndpoint (lowerChild p ([2], [2])) false := by
      rw [← not_le]
      exact fun hlo => hp ⟨hlo, hut⟩
    linarith

#print axioms solution
