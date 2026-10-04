-- Prove2me | solution 1 for AvramDividend.Classical.discounted_positive_jump_tail_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T22:32:12.131919+00:00
-- url     : https://prove2.me/submissions/6264615b-5c14-4261-afd1-6b95ee3c3f81

import Mathlib
import Theorems.Thm_AvramDividend_Classical_positive_jump_tail_laplace_layercake
import Theorems.Thm_AvramDividend_Classical_discounted_interval_exp_identity

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (μ : Measure ℝ≥0) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ t in Ioi (0 : ℝ),
       μ {z : ℝ≥0 | t < (z : ℝ)} *
         ENNReal.ofReal (Real.exp (-θ * t))) =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal ((1 - Real.exp (-θ * (z : ℝ))) / θ) ∂μ := by
  calc
    _ = ∫⁻ z : ℝ≥0,
        ENNReal.ofReal
          (∫ t in (0 : ℝ)..(z : ℝ), Real.exp (-θ * t)) ∂μ :=
      (positive_jump_tail_laplace_layercake μ θ hθ).symm
    _ = ∫⁻ z : ℝ≥0,
        ENNReal.ofReal ((1 - Real.exp (-θ * (z : ℝ))) / θ) ∂μ := by
      apply lintegral_congr
      intro z
      rw [discounted_interval_exp_identity θ (z : ℝ) hθ]
