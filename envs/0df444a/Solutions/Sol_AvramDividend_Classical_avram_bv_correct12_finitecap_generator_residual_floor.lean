-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_finitecap_generator_residual_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:00:30.018524+00:00
-- url     : https://prove2.me/submissions/8d132a31-899c-46bf-a6cf-77a7e0391346

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite-cap original HJB residual has a finite lower bound without global positivity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ z < 0, w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hMass : X.ν (Iio (0 : ℝ)) < ⊤)
    (hDrift : 0 ≤ X.drift)
    (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C)
    (hGen : X.GeneratorIntegrable w y) :
    -((X.ν (Iio (0 : ℝ))).toReal + q) * w y ≤
      X.generator w y - q * w y := by
  classical
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hMass⟩
  have hValues :=
    avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
      C hC w hw_cont hw0 hw_smooth hw_grad y (le_of_lt hy) hyC
  have hNonneg : ∀ z : ℝ, z < 0 → 0 ≤ w (y + z) := by
    intro z hz
    by_cases hpos : 0 ≤ y + z
    · exact hValues (y + z) (by constructor <;> linarith)
    · rw [hw_neg (y + z) (lt_of_not_ge hpos)]
  have hConst : Integrable (fun _ : ℝ => -w y) μ := integrable_const _
  have hIncr : Integrable (fun z : ℝ => w (y + z) - w y) μ := by
    simpa [μ, IntegrableOn] using
      (boundedVariation_full_negative_jump_increment_integrable X hBV w y hGen)
  have hSupport : ∀ᵐ z ∂μ, z < 0 := by
    filter_upwards [ae_restrict_mem (measurableSet_Iio : MeasurableSet (Iio (0 : ℝ)))] with z hz
    exact hz
  have hMono :
      (∫ _ : ℝ, -w y ∂μ) ≤
        (∫ z : ℝ, w (y + z) - w y ∂μ) := by
    apply integral_mono_ae hConst hIncr
    filter_upwards [hSupport] with z hz
    linarith [hNonneg z hz]
  have hJump :
      -((X.ν (Iio (0 : ℝ))).toReal) * w y ≤
        (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν) := by
    simpa [μ, integral_const, Measure.real_def, smul_eq_mul, mul_comm,
      mul_left_comm, mul_assoc] using hMono
  have hRep :=
    boundedVariation_generator_physical_drift_representation X hBV w y hGen
  have hPositive : 0 ≤ X.drift * deriv w y :=
    mul_nonneg hDrift (le_trans (by norm_num : (0 : ℝ) ≤ 1) (hw_grad y hy hyC))
  rw [hRep]
  nlinarith
