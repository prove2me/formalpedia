-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_correct12_finite_activity_uniform_zero_gradient_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T22:20:13.88081+00:00
-- url     : https://prove2.me/submissions/d42481fe-f1bf-4d8c-89b1-d6a9fe25a177

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_local_generator_drift_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! An actual finite-activity BV HJB gives a derivative bound uniform down to zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (b : ℝ) (hb : 0 ≤ b) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ y : ℝ, 0 < y → y ≤ b → ENNReal.ofReal y < C → deriv w y ≤ L := by
  classical
  obtain ⟨R, hR0, hR⟩ :=
    avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
      w hw_cont hw_neg b hb
  have hdpos : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  have hrate : 0 ≤ q + (X.ν (Iio (0 : ℝ))).toReal :=
    add_nonneg (le_of_lt hq) ENNReal.toReal_nonneg
  refine ⟨(q + (X.ν (Iio (0 : ℝ))).toReal) * R / X.drift,
    div_nonneg (mul_nonneg hrate hR0) (le_of_lt hdpos), ?_⟩
  intro y hy hyb hyC
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
  obtain ⟨hInt, hHJB⟩ := hw_gen y hy hyC
  have hDrift :=
    avram_bv_correct12_finite_activity_local_generator_drift_bound
      X hBV hFinite q w y hInt hHJB hLocal
  have hwUpper : w y ≤ R := (le_abs_self (w y)).trans (hR y hyb)
  have hD : X.drift * deriv w y ≤
      (q + (X.ν (Iio (0 : ℝ))).toReal) * R :=
    hDrift.trans (mul_le_mul_of_nonneg_left hwUpper hrate)
  apply (le_div_iff₀ hdpos).2
  nlinarith [hD]
