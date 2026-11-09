-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_finite_activity_positive_cap_HJB_drift_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T20:23:44.767956+00:00
-- url     : https://prove2.me/submissions/3305871d-472f-42a5-a5ff-089c5323a504

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_local_generator_drift_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (y : ℝ) (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    X.drift ≤ (q + (X.ν (Iio (0 : ℝ))).toReal) * w y := by
  classical
  have hDrift : 0 ≤ X.drift :=
    le_of_lt (bv_standing_drift_pos X hX hBV).1
  have hEnvelope :=
    avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
      C hC w hw_cont hw_smooth hw_grad y (le_of_lt hy) hyC
  have hLocal : ∀ z : ℝ, z < 0 → 0 ≤ w (y + z) := by
    intro z hz
    by_cases hneg : y + z < 0
    · simp [hw_neg (y + z) hneg]
    · have hle : y + z ≤ y := by linarith
      have hmem : y + z ∈ Icc (0 : ℝ) y :=
        ⟨le_of_not_gt hneg, hle⟩
      have hBound := hEnvelope (y + z) hmem
      linarith
  have hGen := hw_gen y hy hyC
  have hBound :=
    avram_bv_correct12_finite_activity_local_generator_drift_bound
      X hBV hFinite q w y hGen.1 hGen.2 hLocal
  have hDerivative := hw_grad y hy hyC
  have hDriftBound : X.drift ≤ X.drift * deriv w y := by
    nlinarith [mul_nonneg hDrift (sub_nonneg.mpr hDerivative)]
  linarith
