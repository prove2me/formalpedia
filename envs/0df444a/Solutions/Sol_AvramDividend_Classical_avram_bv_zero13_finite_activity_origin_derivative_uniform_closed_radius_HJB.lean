-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_zero13_finite_activity_origin_derivative_uniform_closed_radius_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:15:21.281115+00:00
-- url     : https://prove2.me/submissions/12596187-ae63-4c27-8730-b864c868055b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_local_generator_drift_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_gradient_linear_lower_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite negative activity makes the original interior HJB derivative
uniformly bounded on the open positive radius through either boundary. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε ≤ C) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, 0 < y → y < ε → |deriv w y| ≤ K := by
  have hd : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  have hν : 0 ≤ (X.ν (Iio (0 : ℝ))).toReal := ENNReal.toReal_nonneg
  have hr : 0 ≤ q + (X.ν (Iio (0 : ℝ))).toReal := by linarith
  have hsec :=
    avram_wave7_02_original_positive_cap_C1_closed_endpoint_two_point_jump_envelope
      C hC w hw_cont hw_smooth hw_grad ε (le_of_lt hε) hεC
  have hlinear : ∀ y ∈ Icc (0 : ℝ) ε, w 0 + y ≤ w y := by
    intro y hy
    have h := hsec 0 ⟨le_refl _, le_of_lt hε⟩ y hy hy.1
    linarith
  have hwε : 0 ≤ w ε := by
    have h := hlinear ε ⟨le_of_lt hε, le_refl ε⟩
    linarith
  let K : ℝ := ((q + (X.ν (Iio (0 : ℝ))).toReal) * w ε) / X.drift
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    exact div_nonneg (mul_nonneg hr hwε) (le_of_lt hd)
  intro y hy hyε
  have hyC : ENNReal.ofReal y < C :=
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hy.le).2 hyε).trans_le hεC
  have hLocal : ∀ z : ℝ, z < 0 → 0 ≤ w (y + z) := by
    intro z hz
    by_cases hneg : y + z < 0
    · simpa [hw_neg (y + z) hneg]
    · have hnonneg : 0 ≤ y + z := le_of_not_gt hneg
      have hle : y + z ≤ ε := by linarith
      have h := hlinear (y + z) ⟨hnonneg, hle⟩
      linarith
  obtain ⟨hGen, hHJB⟩ := hw_gen y hy hyC
  have hG := avram_bv_correct12_finite_activity_local_generator_drift_bound
    X hBV hFinite q w y hGen hHJB hLocal
  have hwyle : w y ≤ w ε := by
    have h := hsec y ⟨le_of_lt hy, le_of_lt hyε⟩
      ε ⟨le_of_lt hε, le_refl ε⟩ (le_of_lt hyε)
    linarith
  have hdrift :
      X.drift * deriv w y ≤
        (q + (X.ν (Iio (0 : ℝ))).toReal) * w ε := by
    exact le_trans hG (mul_le_mul_of_nonneg_left hwyle hr)
  have hderiv : 0 ≤ deriv w y := by
    have hgr := hw_grad y hy hyC
    linarith
  rw [abs_of_nonneg hderiv]
  dsimp [K]
  apply (le_div_iff₀ hd).2
  nlinarith
