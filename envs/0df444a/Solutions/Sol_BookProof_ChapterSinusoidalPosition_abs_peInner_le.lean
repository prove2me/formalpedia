-- Prove2me | solution 1 for BookProof.ChapterSinusoidalPosition.abs_peInner_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:53:59.185711+00:00
-- url     : https://prove2.me/submissions/e33792af-9a5d-41e6-80f8-25e774276b17

-- Generated from ChapterSinusoidalPosition.lean — solution of BookProof.ChapterSinusoidalPosition.abs_peInner_le
import Mathlib
import Definitions.Def_ChapterSinusoidalPosition
import Theorems.Thm_BookProof_ChapterSinusoidalPosition_peInner_eq_sum_cos
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSinusoidalPosition



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin n → ℝ) (p q : ℝ) : |peInner w p q| ≤ (n : ℝ) := by

  rw [peInner_eq_sum_cos]
  calc |∑ a, Real.cos (w a * (p - q))| ≤ ∑ a, |Real.cos (w a * (p - q))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin n, (1 : ℝ) := Finset.sum_le_sum fun a _ => Real.abs_cos_le_one _
    _ = (n : ℝ) := by simp
