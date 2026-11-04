-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_finite_separated_band_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:35:32.140223+00:00
-- url     : https://prove2.me/submissions/30998838-ae15-498c-9425-da5373a5bfdd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The source Levy prescribed separated-band rate is finite on
all finite nonnegative horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    (T : ℝ≥0∞) * X.ν B < ⊤ := by
  apply ENNReal.mul_lt_top ENNReal.coe_lt_top
  exact avram_p2_a_zero_rate_separated_borel_nu_finite X B hB ε hε hBsep
