-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_negative_mark_exponential_mass_between_zero_and_rate_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:30:32.141206+00:00
-- url     : https://prove2.me/submissions/6cb24aa4-0122-40f2-afe8-f45429981d83

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_finite_negative_mark_exponential_integrable_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The finite negative-mark exponential mass is between zero and total jump intensity. -/
theorem solution (ν : Measure ℝ)
    (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    0 ≤ (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂ν) ∧
    (∫ y in Iio (0 : ℝ), Real.exp (θ * y) ∂ν) ≤
      (ν (Iio (0 : ℝ))).toReal := by
  let μ : Measure ℝ := ν.restrict (Iio (0 : ℝ))
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using hFinite⟩
  have hExp : Integrable (fun y : ℝ => Real.exp (θ * y)) μ :=
    avram_a27_finite_negative_mark_exponential_integrable_20261117
      ν hFinite θ hθ
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) μ :=
    integrable_const 1
  have hBound :
      ∀ᵐ y ∂μ, Real.exp (θ * y) ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    exact (Real.exp_le_one_iff).2
      (mul_nonpos_of_nonneg_of_nonpos hθ (le_of_lt hy))
  have hNonNeg : 0 ≤ ∫ y, Real.exp (θ * y) ∂μ :=
    integral_nonneg (fun y => le_of_lt (Real.exp_pos _))
  have hTop : (∫ y, Real.exp (θ * y) ∂μ) ≤
      (∫ _ : ℝ, (1 : ℝ) ∂μ) :=
    integral_mono_ae hExp hone hBound
  change 0 ≤ (∫ y, Real.exp (θ * y) ∂μ) ∧
    (∫ y, Real.exp (θ * y) ∂μ) ≤ (ν (Iio (0 : ℝ))).toReal
  refine ⟨hNonNeg, ?_⟩
  calc
    _ ≤ (∫ _ : ℝ, (1 : ℝ) ∂μ) := hTop
    _ = (ν (Iio (0 : ℝ))).toReal := by
      simp [μ, measureReal_def]
