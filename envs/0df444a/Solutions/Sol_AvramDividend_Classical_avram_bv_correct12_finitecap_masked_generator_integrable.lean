-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_finitecap_masked_generator_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:24:08.1314+00:00
-- url     : https://prove2.me/submissions/81971556-c8a2-4010-9f90-16713d6a003d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finitecap_generator_residual_floor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite-activity source sampled inside the original finite cap is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ z < 0, w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C →
      1 ≤ deriv w z)
    (hMass : X.ν (Iio (0 : ℝ)) < ⊤)
    (Y : Ω → ℝ) (mask : Ω → Prop)
    (hYI : Integrable (fun ω => w (Y ω)) P)
    (hInside : ∀ ω, mask ω →
      0 < Y ω ∧ ENNReal.ofReal (Y ω) < C ∧
      X.GeneratorIntegrable w (Y ω) ∧
      X.generator w (Y ω) - q * w (Y ω) ≤ 0)
    (hMeas : AEStronglyMeasurable (fun ω =>
      if mask ω then X.generator w (Y ω) - q * w (Y ω) else 0) P) :
    Integrable (fun ω =>
      if mask ω then X.generator w (Y ω) - q * w (Y ω) else 0) P := by
  classical
  have hCoeff : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal + q :=
    add_nonneg ENNReal.toReal_nonneg hq.le
  have hAbsI : Integrable (fun ω => |w (Y ω)|) P := by
    simpa only [Real.norm_eq_abs] using hYI.norm
  have hMajor : Integrable (fun ω =>
      ((X.ν (Iio (0 : ℝ))).toReal + q) * |w (Y ω)|) P := by
    simpa only [smul_eq_mul] using hAbsI.const_mul
      ((X.ν (Iio (0 : ℝ))).toReal + q)
  apply hMajor.mono' hMeas
  filter_upwards [] with ω
  by_cases hm : mask ω
  · obtain ⟨hy, hyC, hGen, hUpper⟩ := hInside ω hm
    have hValues :=
      avram_wave7_02_original_positive_cap_C1_gradient_value_nonnegative_on_compact_interval
        C hC w hw_cont hw0 hw_smooth hw_grad (Y ω) (le_of_lt hy) hyC
    have hYnonneg : 0 ≤ w (Y ω) :=
      hValues (Y ω) ⟨le_of_lt hy, le_rfl⟩
    have hLower := avram_bv_correct12_finitecap_generator_residual_floor
      X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad hMass
        (bv_standing_drift_pos X hX hBV).1.le (Y ω) hy hyC hGen
    simp only [if_pos hm, Real.norm_eq_abs]
    rw [abs_of_nonpos hUpper, abs_of_nonneg hYnonneg]
    linarith
  · simp only [if_neg hm, Real.norm_eq_abs, abs_zero]
    exact mul_nonneg hCoeff (abs_nonneg _)
