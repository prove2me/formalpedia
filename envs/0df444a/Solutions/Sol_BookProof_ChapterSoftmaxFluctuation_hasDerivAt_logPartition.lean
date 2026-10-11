-- Prove2me | solution 1 for BookProof.ChapterSoftmaxFluctuation.hasDerivAt_logPartition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:29:46.048568+00:00
-- url     : https://prove2.me/submissions/6735f812-de6e-4f89-a8b6-d9e85b003590

-- Generated from ChapterSoftmaxFluctuation.lean — solution of BookProof.ChapterSoftmaxFluctuation.hasDerivAt_logPartition
import Mathlib
import Definitions.Def_ChapterSoftmaxFluctuation
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_partition_ne_zero
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_scoreSoftmax_eq_div
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_partition
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun b : ℝ => logPartition b s) (meanScore beta s) beta := by

  have hZ := hasDerivAt_partition beta s
  have hne := partition_ne_zero beta s i
  have h := hZ.log hne
  refine h.congr_deriv ?_
  rw [meanScore, Finset.sum_div]
  exact Finset.sum_congr rfl fun l _ => by
    rw [scoreSoftmax_eq_div, div_mul_eq_mul_div, mul_comm (Real.exp (beta * s l)) (s l)]
