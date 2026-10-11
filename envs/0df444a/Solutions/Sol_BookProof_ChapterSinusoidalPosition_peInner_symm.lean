-- Prove2me | solution 1 for BookProof.ChapterSinusoidalPosition.peInner_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:53:57.16933+00:00
-- url     : https://prove2.me/submissions/d79e54f9-d4fe-4dc2-8109-2a41d80e7bed

-- Generated from ChapterSinusoidalPosition.lean — solution of BookProof.ChapterSinusoidalPosition.peInner_symm
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
theorem solution (w : Fin n → ℝ) (p q : ℝ) : peInner w p q = peInner w q p := by

  rw [peInner_eq_sum_cos, peInner_eq_sum_cos]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [show w a * (q - p) = -(w a * (p - q)) by ring, Real.cos_neg]
