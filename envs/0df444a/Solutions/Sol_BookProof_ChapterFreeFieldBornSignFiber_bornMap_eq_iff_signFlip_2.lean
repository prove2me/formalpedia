-- Prove2me | solution 2 for BookProof.ChapterFreeFieldBornSignFiber.bornMap_eq_iff_signFlip
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:27:01.245876+00:00
-- url     : https://prove2.me/submissions/b1e7b6ac-b91e-4f7a-9fb9-085483a342f0

import Mathlib
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornSignFiber

variable {n : ℕ}

open MeasureTheory BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSignGauge BookProof.ChapterFreeFieldBornSignFiber in
theorem solution (x y : EuclideanSpace ℝ (Fin n)) :
    bornMap y = bornMap x ↔
      ∃ s : Fin n → ℝ, (∀ k, s k = 1 ∨ s k = -1) ∧ y = signFlip s x := by
  constructor
  · intro h
    refine ⟨fun k => if y k = x k then 1 else -1, fun k => ?_, ?_⟩
    · by_cases hk : y k = x k <;> simp [hk]
    · refine PiLp.ext fun k => ?_
      have hk : y k ^ 2 = x k ^ 2 := congrFun h k
      rw [signFlip_apply]
      by_cases e : y k = x k
      · simp [e]
      · simp only [e, if_false]
        rcases sq_eq_sq_iff_eq_or_eq_neg.mp hk with h1 | h1
        · exact absurd h1 e
        · rw [h1]; ring
  · rintro ⟨s, hs, rfl⟩
    funext k
    simp only [bornMap, signFlip_apply]
    rcases hs k with h | h <;> rw [h] <;> ring
