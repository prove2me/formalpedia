-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_original_rescaled_weighted_exp_moments_identify_levy_image
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:20:10.708778+00:00
-- url     : https://prove2.me/submissions/6e1ffa91-a323-437a-bd19-63546bcbd7f2

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_rescaled_weighted_exp_polynomial_moments_converge
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_real_moment_bridge

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original source rescaled moments converge to the actual
compactly-supported negative Levy-image moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    Tendsto
      (fun h : ℝ => (ENNReal.ofReal h)⁻¹ *
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
          ((P.withDensity (fun ω => ENNReal.ofReal
            ((Real.exp (X.X (Real.toNNReal h) ω) - 1) ^ 4))).map
            (fun ω => Real.exp (X.X (Real.toNNReal h) ω)))))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
        (((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
          Real.exp))) := by
  simpa only [← avram_p2_negative_levy_weighted_exp_real_moment_bridge X k] using
    (avram_p2_original_rescaled_weighted_exp_polynomial_moments_converge X k)
