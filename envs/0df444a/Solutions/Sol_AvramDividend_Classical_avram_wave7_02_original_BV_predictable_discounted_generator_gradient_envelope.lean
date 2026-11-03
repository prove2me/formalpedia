-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_predictable_discounted_generator_gradient_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:35:42.032405+00:00
-- url     : https://prove2.me/submissions/80b7c490-8dac-460e-8078-5387f3a68b91

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The original bounded-variation generator has nonpositive physical drift
and dividend-density HJB corrections at the actual controlled predictable
left-limit reserve, with the correct positive discount multiplier. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0)
    (hregion :
      0 < Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) < C) :
    let y := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    X.GeneratorIntegrable w y ∧
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w y +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y) ≤ 0 ∧
    Real.exp (-(q * (t : ℝ))) * (1 - deriv w y) ≤ 0 := by
  let y : ℝ := Function.leftLim
    (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
  change X.GeneratorIntegrable w y ∧
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w y +
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y) ≤ 0 ∧
    Real.exp (-(q * (t : ℝ))) * (1 - deriv w y) ≤ 0
  obtain ⟨hInt, hNonpos⟩ := hw_gen y hregion.1 hregion.2
  have hRep :=
    boundedVariation_generator_physical_drift_representation X hBV w y hInt
  have hPhysical : X.drift * deriv w y +
      (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) - q * w y ≤ 0 := by
    simpa only [hRep] using hNonpos
  have hSlope : 1 - deriv w y ≤ 0 := by
    linarith [hw_grad y hregion.1 hregion.2]
  have hDiscount : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  exact ⟨hInt,
    mul_nonpos_of_nonneg_of_nonpos hDiscount hPhysical,
    mul_nonpos_of_nonneg_of_nonpos hDiscount hSlope⟩
