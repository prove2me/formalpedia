-- Prove2me | solution 1 for AvramDividend.Classical.avram_b0dd16_finite_activity_generator_residual_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T16:53:20.509323+00:00
-- url     : https://prove2.me/submissions/d2a923fe-c0ee-4617-a18c-55904c555ba3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (y : ℝ)
    (hGen : X.GeneratorIntegrable w y)
    (hMass : X.ν (Iio (0 : ℝ)) < ⊤)
    (hW : ∀ z : ℝ, 0 ≤ w z)
    (hDrift : 0 ≤ X.drift)
    (hDeriv : 0 ≤ deriv w y) :
    -((X.ν (Iio (0 : ℝ))).toReal + q) * w y ≤
      X.generator w y - q * w y := by
  classical
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hMass⟩
  have hConst : Integrable (fun _ : ℝ => -w y) μ :=
    integrable_const _
  have hIncr : Integrable (fun z : ℝ => w (y + z) - w y) μ := by
    simpa [μ, IntegrableOn] using
      (boundedVariation_full_negative_jump_increment_integrable X hBV w y hGen)
  have hMono :
      (∫ _ : ℝ, -w y ∂μ) ≤
        (∫ z : ℝ, w (y + z) - w y ∂μ) := by
    apply integral_mono_ae hConst hIncr
    filter_upwards [] with z
    linarith [hW (y + z)]
  have hJump :
      -((X.ν (Iio (0 : ℝ))).toReal) * w y ≤
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) := by
    simpa [μ, integral_const, Measure.real_def, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using hMono
  have hRep :=
    boundedVariation_generator_physical_drift_representation X hBV w y hGen
  have hPositive : 0 ≤ X.drift * deriv w y := mul_nonneg hDrift hDeriv
  rw [hRep]
  nlinarith
