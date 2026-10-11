-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.weightedVar_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:32:24.047651+00:00
-- url     : https://prove2.me/submissions/65b15882-16e0-4bc9-a899-1239b4bb9ea3

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.weightedVar_nonneg
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Theorems.Thm_BookProof_ChapterSoftmaxJacobian_weightedVar_eq_sum_sq
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_pos
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s x : Fin m → ℝ) (i : Fin m) :
    0 ≤ weightedVar beta s x := by

  rw [weightedVar_eq_sum_sq beta s x i]
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (le_of_lt (scoreSoftmax_pos beta s j)) (sq_nonneg _)
