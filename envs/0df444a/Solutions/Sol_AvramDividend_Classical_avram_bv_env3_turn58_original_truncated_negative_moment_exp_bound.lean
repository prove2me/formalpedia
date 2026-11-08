-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn58_original_truncated_negative_moment_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:33:30.114205+00:00
-- url     : https://prove2.me/submissions/3898bbf9-f069-4d65-86d4-9b11f50a4504

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_min_abs_integrable
import Theorems.Thm_AvramDividend_Classical_negative_exponential_quotient_bounds
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn57_min_le_exp_deficit
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Transfer the scalar exponential-deficit bound to the original negative Levy measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν) ≤
      2 * (∫ z in Iio (0 : ℝ),
        (1 - Real.exp (ε⁻¹ * z)) / ε⁻¹ ∂X.ν) := by
  have hθpos : 0 < ε⁻¹ := inv_pos.mpr hε
  have hθone : (1 : ℝ) ≤ ε⁻¹ := by
    rw [← one_div]; exact (le_div_iff₀ hε).mpr (by simpa using hε1)
  have hmem : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ∈ Iio (0 : ℝ) := ae_restrict_mem measurableSet_Iio
  have hint := chat07_bv_negative_jump_min_abs_integrable X hBV
  have hright : IntegrableOn
      (fun z : ℝ => (1 - Real.exp (ε⁻¹ * z)) / ε⁻¹)
      (Iio (0 : ℝ)) X.ν := by
    change Integrable (fun z : ℝ => (1 - Real.exp (ε⁻¹ * z)) / ε⁻¹)
      (X.ν.restrict (Iio (0 : ℝ)))
    change Integrable (fun z : ℝ => min (1 : ℝ) |z|)
      (X.ν.restrict (Iio (0 : ℝ))) at hint
    apply hint.mono (by fun_prop : Continuous (fun z : ℝ =>
      (1 - Real.exp (ε⁻¹ * z)) / ε⁻¹)).aestronglyMeasurable
    filter_upwards [hmem] with z hz
    change z < (0 : ℝ) at hz
    have hq := negative_exponential_quotient_bounds ε⁻¹ z hθpos hz
    have hqone : (1 - Real.exp (ε⁻¹ * z)) / ε⁻¹ ≤ 1 := by
      apply (div_le_iff₀ hθpos).mpr
      linarith [Real.exp_pos (ε⁻¹ * z)]
    have hbound : (1 - Real.exp (ε⁻¹ * z)) / ε⁻¹ ≤
        min (1 : ℝ) |z| := by
      exact le_min hqone (by simpa [abs_of_neg hz] using hq.2)
    have hm : 0 ≤ min (1 : ℝ) |z| := le_min (by norm_num) (abs_nonneg z)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hq.1, abs_of_nonneg hm]
      using hbound
  have hleft : IntegrableOn (fun z : ℝ => min ε (-z)) (Iio (0 : ℝ)) X.ν :=
    avram_route_bv_drift9_original_spatial_truncated_first_moment_L1 X hBV ε hε hε1
  have hpoint (z : ℝ) (hz : z < 0) :
      min ε (-z) ≤ 2 * ((1 - Real.exp (ε⁻¹ * z)) / ε⁻¹) := by
    have ht : 0 ≤ ε⁻¹ * (-z) := mul_nonneg hθpos.le (by linarith)
    have hc : ε * ε⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hε)
    have hsc := avram_bv_env3_turn57_min_le_exp_deficit (ε⁻¹ * (-z)) ht
    have hscale : min ε (-z) = ε * min 1 (ε⁻¹ * (-z)) := by
      have hid : ε * (ε⁻¹ * (-z)) = -z := by rw [← mul_assoc, hc, one_mul]
      rcases le_total (1 : ℝ) (ε⁻¹ * (-z)) with h | h
      · have he : ε ≤ -z := by
          calc
            ε = ε * 1 := by ring
            _ ≤ ε * (ε⁻¹ * (-z)) := mul_le_mul_of_nonneg_left h hε.le
            _ = -z := hid
        rw [min_eq_left he, min_eq_left h]; ring
      · have he : -z ≤ ε := by
          calc
            -z = ε * (ε⁻¹ * (-z)) := hid.symm
            _ ≤ ε * 1 := mul_le_mul_of_nonneg_left h hε.le
            _ = ε := by ring
        simpa only [min_eq_right he, min_eq_right h] using hid.symm
    calc
      min ε (-z) = ε * min 1 (ε⁻¹ * (-z)) := hscale
      _ ≤ ε * (2 * (1 - Real.exp (-(ε⁻¹ * (-z))))) :=
        mul_le_mul_of_nonneg_left hsc hε.le
      _ = 2 * ((1 - Real.exp (ε⁻¹ * z)) / ε⁻¹) := by
        rw [show -(ε⁻¹ * (-z)) = ε⁻¹ * z by ring, div_eq_mul_inv, inv_inv]
        ring
  have hle : (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν) ≤
      ∫ z in Iio (0 : ℝ), 2 * ((1 - Real.exp (ε⁻¹ * z)) / ε⁻¹) ∂X.ν := by
    apply integral_mono_ae hleft (hright.const_mul 2)
    filter_upwards [hmem] with z hz
    change z < (0 : ℝ) at hz
    exact hpoint z hz
  simpa only [integral_const_mul] using hle
