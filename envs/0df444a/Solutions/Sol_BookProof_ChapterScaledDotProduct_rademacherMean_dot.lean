-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.rademacherMean_dot
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:22:45.058384+00:00
-- url     : https://prove2.me/submissions/9dfaa6b9-95a2-4837-b67f-5cd73c0c97c9

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.rademacherMean_dot
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
import Theorems.Thm_BookProof_ChapterScaledDotProduct_sum_sgn_eq_zero
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterScaledDotProduct



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (k : Fin d → ℝ) :
    rademacherMean (fun x => dot (signVec x) k) = 0 := by

  have hswap : ∑ x : (Fin d → Bool), dot (signVec x) k
      = ∑ i, (∑ x : (Fin d → Bool), sgn (x i)) * k i := by
    simp only [dot, signVec, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [rademacherMean, hswap]
  simp [sum_sgn_eq_zero]
