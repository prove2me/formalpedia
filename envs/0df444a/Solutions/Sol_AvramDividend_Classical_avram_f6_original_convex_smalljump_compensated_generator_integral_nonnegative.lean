-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_convex_smalljump_compensated_generator_integral_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:37:31.073874+00:00
-- url     : https://prove2.me/submissions/a35f9fd2-4619-45d5-8930-98e285856747

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_convex_smalljump_generator_integrand_nonnegative
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hConvex : ConvexOn ℝ Set.univ w)
    (y : ℝ) (hDiff : DifferentiableAt ℝ w y) :
    0 ≤ ∫ z in Ioo (-1 : ℝ) 0,
      SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
  exact avram_f6_original_convex_smalljump_generator_integrand_nonnegative
    w hConvex y z hDiff hz.1 hz.2
