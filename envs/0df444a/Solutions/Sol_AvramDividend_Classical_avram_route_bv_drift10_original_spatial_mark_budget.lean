-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_bv_drift10_original_spatial_mark_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:36:57.086106+00:00
-- url     : https://prove2.me/submissions/0419cbe3-3f60-458f-886a-238c712ad5f7

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_negative_mark_loss_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_each_mark_spatial_loss_le

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
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) (hε1 : ε ≤ 1) :
    (∫ z in Iio (0 : ℝ), (∫ y in Ioc (0 : ℝ) ε,
      w y - w (y + z) ∂(volume : Measure ℝ)) ∂X.ν) ≤
    (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν) * w ε := by
  have hpos : 0 ≤ᵐ[X.ν.restrict (Iio (0 : ℝ))]
      (fun z : ℝ => ∫ y in Ioc (0 : ℝ) ε,
        w y - w (y + z) ∂(volume : Measure ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact avram_route_bv_drift9_original_negative_mark_loss_nonneg
      C hC w hw_cont hw0 hw_neg hw_smooth hw_grad ε hε hεC y hy z hz
  have hle : (fun z : ℝ => ∫ y in Ioc (0 : ℝ) ε,
        w y - w (y + z) ∂(volume : Measure ℝ))
      ≤ᵐ[X.ν.restrict (Iio (0 : ℝ))]
      (fun z : ℝ => min ε (-z) * w ε) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    exact avram_route_bv_drift9_each_mark_spatial_loss_le
      C hC w hw_cont hw0 hw_neg hw_smooth hw_grad hwzero ε hε hεC z hz
  have hmajor : IntegrableOn (fun z : ℝ => min ε (-z) * w ε)
      (Iio (0 : ℝ)) X.ν :=
    (avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
      X hBV ε hε hε1).mul_const (w ε)
  calc
    (∫ z in Iio (0 : ℝ), (∫ y in Ioc (0 : ℝ) ε,
      w y - w (y + z) ∂(volume : Measure ℝ)) ∂X.ν)
      ≤ (∫ z in Iio (0 : ℝ), min ε (-z) * w ε ∂X.ν) :=
        integral_mono_of_nonneg hpos hmajor hle
    _ = (∫ z in Iio (0 : ℝ), min ε (-z) ∂X.ν) * w ε := by
      exact integral_mul_const (w ε) (fun z : ℝ => min ε (-z))
