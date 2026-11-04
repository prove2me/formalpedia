-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_tilt_lintegral_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:48:30.758241+00:00
-- url     : https://prove2.me/submissions/f86e3198-f9ad-4614-8f41-26c78fe97670

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- All exponentially tilted fourth-weighted negative Lévy moments are
bounded by the untilted mass, the moment comparison needed at the limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (Real.exp (ρ * y) * (Real.exp y - 1) ^ 4) ∂X.ν) ≤
    (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal ((Real.exp y - 1) ^ 4) ∂X.ν) := by
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
  have hy0 : y ≤ 0 := le_of_lt hy
  have hmul : ρ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ hy0
  have hexp : Real.exp (ρ * y) ≤ 1 := Real.exp_le_one_iff.mpr hmul
  have hw : 0 ≤ (Real.exp y - 1) ^ 4 := by positivity
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.exp (ρ * y) * (Real.exp y - 1) ^ 4 ≤
      1 * (Real.exp y - 1) ^ 4 :=
        mul_le_mul_of_nonneg_right hexp hw
    _ = (Real.exp y - 1) ^ 4 := one_mul _
