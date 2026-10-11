-- Prove2me | solution 1 for BookProof.ChapterSoftmaxSharpness.scoreSoftmax_eq_inv_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:41.935224+00:00
-- url     : https://prove2.me/submissions/dfdda85a-572f-4a0f-9e3a-0920b0a8b674

-- Generated from ChapterSoftmaxSharpness.lean — solution of BookProof.ChapterSoftmaxSharpness.scoreSoftmax_eq_inv_sum
import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness



open scoped BigOperators

noncomputable section


open Filter Topology BookProof.ChapterSoftmaxBorn

variable {n m : ℕ}

variable {n m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta s j = 1 / ∑ l, Real.exp (beta * (s l - s j)) := by

  have hfac : ∑ l, Real.exp (beta * s l)
      = Real.exp (beta * s j) * ∑ l, Real.exp (beta * (s l - s j)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Real.exp_add]
    ring_nf
  rw [scoreSoftmax, hfac, mul_comm, ← div_div, div_self (Real.exp_ne_zero _)]
