-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_bv_drift9_original_spatial_jump_loss_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:41:57.886648+00:00
-- url     : https://prove2.me/submissions/35bb72cd-1d4d-4d7a-aeae-7eed21fd9d37

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_zero_extended_value_continuous
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_original_spatial_jump_product_L1
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_original_spatial_jump_tonelli_swap
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_original_spatial_mark_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) (hε1 : ε ≤ 1) :
    (∫ y in Ioc (0 : ℝ) ε,
      (q * w y - (∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν))
      ∂(volume : Measure ℝ)) ≤
    (q * ε + (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν)) * w ε := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) ε)
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : SFinite ν := levy_negative_jump_measure_sFinite X
  have hcontinuous : Continuous w :=
    avram_route_bv_drift10_zero_extended_value_continuous w hw_cont hw_neg hwzero
  have hqI : Integrable (fun y : ℝ => q * w y) μ := by
    have hc : Continuous (fun y : ℝ => q * w y) := continuous_const.mul hcontinuous
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hJ : Integrable (fun y : ℝ => ∫ z, w y - w (y + z) ∂ν) μ :=
    (avram_route_bv_drift10_original_spatial_jump_product_L1
      X hBV w C hC hw_cont hw0 hw_neg hw_smooth hw_grad hwzero
        ε hε hεC hε1).integral_prod_left
  have hsec : ∀ᵐ y ∂μ, w y ≤ w ε := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have hs := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad y ε (le_of_lt hy.1) hy.2 (le_of_lt hεC)
    linarith [sub_nonneg.mpr hy.2]
  have hqBound : (∫ y, q * w y ∂μ) ≤ q * ε * w ε := by
    have hpoint : (fun y : ℝ => q * w y) ≤ᵐ[μ] (fun _ => q * w ε) := by
      filter_upwards [hsec] with y hy
      exact mul_le_mul_of_nonneg_left hy hq.le
    calc
      (∫ y, q * w y ∂μ) ≤ ∫ y, q * w ε ∂μ :=
        integral_mono_ae hqI (integrable_const _) hpoint
      _ = ε * (q * w ε) := by
        dsimp [μ]
        rw [setIntegral_const, Real.volume_real_Ioc_of_le hε.le, sub_zero]
        simp only [smul_eq_mul]
      _ = q * ε * w ε := by ring
  have hpoint (y : ℝ) : q * w y - (∫ z, w (y + z) - w y ∂ν) =
      q * w y + (∫ z, w y - w (y + z) ∂ν) := by
    have hneg : (fun z : ℝ => w (y + z) - w y) = fun z => -(w y - w (y + z)) := by
      funext z; ring
    rw [hneg, integral_neg]; ring
  have hFubini := avram_route_bv_drift10_original_spatial_jump_tonelli_swap
    X hBV w C hC hw_cont hw0 hw_neg hw_smooth hw_grad hwzero ε hε hεC hε1
  have hMark := avram_route_bv_drift10_original_spatial_mark_budget
    X hBV w C hC hw_cont hw0 hw_neg hw_smooth hw_grad hwzero ε hε hεC hε1
  calc
    (∫ y, q * w y - (∫ z, w (y + z) - w y ∂ν) ∂μ)
      = ∫ y, q * w y + (∫ z, w y - w (y + z) ∂ν) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (∫ y, q * w y ∂μ) + (∫ y, ∫ z, w y - w (y + z) ∂ν ∂μ) :=
          integral_add hqI hJ
    _ ≤ q * ε * w ε + (∫ y, ∫ z, w y - w (y + z) ∂ν ∂μ) :=
          add_le_add_left hqBound _
    _ = q * ε * w ε + (∫ z, ∫ y, w y - w (y + z) ∂μ ∂ν) := by
          rw [hFubini]
    _ ≤ q * ε * w ε + (∫ z, min ε (-z) ∂ν) * w ε :=
          add_le_add_right hMark _
    _ = (q * ε + (∫ z, min ε (-z) ∂ν)) * w ε := by ring
