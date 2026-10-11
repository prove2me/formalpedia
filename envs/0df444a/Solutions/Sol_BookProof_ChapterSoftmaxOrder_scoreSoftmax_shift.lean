-- Prove2me | solution 1 for BookProof.ChapterSoftmaxOrder.scoreSoftmax_shift
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:30.870474+00:00
-- url     : https://prove2.me/submissions/8460f8f8-dd7d-4ca6-9773-f21f621c4aa6

-- Generated from ChapterSoftmaxOrder.lean — solution of BookProof.ChapterSoftmaxOrder.scoreSoftmax_shift
import Mathlib
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxOrder



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxBorn BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta c : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (fun l => s l + c) j = scoreSoftmax beta s j := by

  have hexp : ∀ l, Real.exp (beta * (s l + c))
      = Real.exp (beta * c) * Real.exp (beta * s l) := by
    intro l
    rw [← Real.exp_add]
    ring_nf
  have hden : (∑ l, Real.exp (beta * (s l + c)))
      = Real.exp (beta * c) * ∑ l, Real.exp (beta * s l) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => hexp l
  rw [scoreSoftmax, scoreSoftmax, hexp j, hden, mul_div_mul_left _ _ (Real.exp_ne_zero _)]
