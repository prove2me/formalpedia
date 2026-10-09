-- Prove2me | solution 1 for BookProof.ChapterCoherentPositionSpace.integral_exp_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:31:11.772148+00:00
-- url     : https://prove2.me/submissions/e1a021cf-1c42-4080-a631-b907a5cb9bae

-- Generated from ChapterCoherentPositionSpace.lean — solution of BookProof.ChapterCoherentPositionSpace.integral_exp_mul_exp
import Mathlib
import Definitions.Def_ChapterCoherentPositionSpace
import Theorems.Thm_BookProof_ChapterCoherentPositionSpace_integral_exp_neg_sq_sub
open BookProof.ChapterCoherentPositionSpace



open scoped BigOperators
open MeasureTheory

noncomputable section


open BookProof.ChapterCoherentOverlap BookProof.ChapterSoftmaxSharpness

set_option maxHeartbeats 1000000 in
theorem solution (a b : ℝ) :
    (∫ x : ℝ, Real.exp (-(x - a) ^ 2 / 2) * Real.exp (-(x - b) ^ 2 / 2))
      = Real.exp (-(a - b) ^ 2 / 4) * Real.sqrt Real.pi := by

  have hpt : ∀ x : ℝ, Real.exp (-(x - a) ^ 2 / 2) * Real.exp (-(x - b) ^ 2 / 2)
      = Real.exp (-(a - b) ^ 2 / 4) * Real.exp (-(x - (a + b) / 2) ^ 2) := by
    intro x
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  calc (∫ x : ℝ, Real.exp (-(x - a) ^ 2 / 2) * Real.exp (-(x - b) ^ 2 / 2))
      = ∫ x : ℝ, Real.exp (-(a - b) ^ 2 / 4) * Real.exp (-(x - (a + b) / 2) ^ 2) :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = Real.exp (-(a - b) ^ 2 / 4) * Real.sqrt Real.pi := by
        rw [MeasureTheory.integral_const_mul, integral_exp_neg_sq_sub]
