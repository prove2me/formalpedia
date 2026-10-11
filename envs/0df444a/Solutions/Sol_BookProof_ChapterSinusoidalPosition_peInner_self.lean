-- Prove2me | solution 1 for BookProof.ChapterSinusoidalPosition.peInner_self
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:53:58.270948+00:00
-- url     : https://prove2.me/submissions/3b0db879-7259-4e74-8a1c-57a5828512b2

-- Generated from ChapterSinusoidalPosition.lean — solution of BookProof.ChapterSinusoidalPosition.peInner_self
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
theorem solution (w : Fin n → ℝ) (p : ℝ) : peInner w p p = (n : ℝ) := by

  rw [peInner_eq_sum_cos]
  simp
