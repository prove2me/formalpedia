-- Prove2me | solution 1 for BookProof.ChapterSoftmaxJacobian.softmaxJacobian_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:32:39.370176+00:00
-- url     : https://prove2.me/submissions/1908d359-55ef-4bf6-a425-5eeebd0ac803

-- Generated from ChapterSoftmaxJacobian.lean — solution of BookProof.ChapterSoftmaxJacobian.softmaxJacobian_posSemidef
import Mathlib
import Definitions.Def_ChapterSoftmaxJacobian
import Theorems.Thm_BookProof_ChapterSoftmaxJacobian_weightedVar_nonneg
import Theorems.Thm_BookProof_ChapterSoftmaxJacobian_softmaxJacobian_quadratic_form
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxJacobian



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {beta : ℝ} (hb : 0 ≤ beta) (s x : Fin m → ℝ) (i : Fin m) :
    0 ≤ ∑ i, ∑ j, x i * softmaxJacobian beta s i j * x j := by

  rw [softmaxJacobian_quadratic_form]
  exact mul_nonneg hb (weightedVar_nonneg beta s x i)
