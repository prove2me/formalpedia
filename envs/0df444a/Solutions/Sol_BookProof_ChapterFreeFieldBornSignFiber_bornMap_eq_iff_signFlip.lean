-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignFiber.bornMap_eq_iff_signFlip
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:29:09.5284+00:00
-- url     : https://prove2.me/submissions/c6599e67-977d-48c4-8ced-a02fd6e04a27

-- Generated from ChapterFreeFieldBornSignFiber.lean — solution of BookProof.ChapterFreeFieldBornSignFiber.bornMap_eq_iff_signFlip
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignFiber
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignGauge_bornMap_signFlip
open BookProof.ChapterFreeFieldBornSignFiber



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSignGauge


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (x y : EuclideanSpace ℝ (Fin n)) :
    bornMap y = bornMap x ↔
      ∃ s : Fin n → ℝ, (∀ k, s k = 1 ∨ s k = -1) ∧ y = signFlip s x := by

  constructor
  · intro h_eq
    have h_sq : ∀ k, (y k) ^ 2 = (x k) ^ 2 := fun k => congr_fun h_eq k
    have h_sign : ∀ k, y k = x k ∨ y k = -x k :=
      fun k => eq_or_eq_neg_of_sq_eq_sq _ _ (h_sq k)
    refine ⟨fun k => if y k = x k then 1 else -1, fun k => ?_, ?_⟩
    · dsimp only; split_ifs <;> norm_num
    · ext k; cases h_sign k <;> simp [*]
  · rintro ⟨s, hs, rfl⟩
    exact bornMap_signFlip hs x
