-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_exp_pushforward_moment_formula
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:25:04.308828+00:00
-- url     : https://prove2.me/submissions/0be872a0-6e08-466e-ad88-117c03b3a62b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Moments of the finite weighted negative Levy exponential image
are exactly the original Levy exponential-transform moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) =
    (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal ((Real.exp y - 1) ^ 4) *
        ENNReal.ofReal ((Real.exp y) ^ k) ∂X.ν) := by
  have hG : Measurable (fun y : ℝ => Real.exp y) :=
    Real.measurable_exp
  have hW : Measurable (fun y : ℝ =>
      ENNReal.ofReal ((Real.exp y - 1) ^ 4)) :=
    ENNReal.measurable_ofReal.comp
      ((hG.sub_const 1).pow_const 4)
  have hF : Measurable (fun z : ℝ => ENNReal.ofReal (z ^ k)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const k)
  calc
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) =
      ∫⁻ y, ENNReal.ofReal ((Real.exp y) ^ k) ∂
        ((X.ν.restrict (Iio (0 : ℝ))).withDensity
          (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))) := by
      exact lintegral_map hF hG
    _ = ∫⁻ y in Iio (0 : ℝ),
        ENNReal.ofReal ((Real.exp y - 1) ^ 4) *
          ENNReal.ofReal ((Real.exp y) ^ k) ∂X.ν := by
      simpa only [Pi.mul_apply, Function.comp_apply] using
        (lintegral_withDensity_eq_lintegral_mul
          (X.ν.restrict (Iio (0 : ℝ))) hW (hF.comp hG))
