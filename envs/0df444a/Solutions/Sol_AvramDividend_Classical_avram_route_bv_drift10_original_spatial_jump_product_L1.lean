-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_bv_drift10_original_spatial_jump_product_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:17:49.63073+00:00
-- url     : https://prove2.me/submissions/62f691f2-99fe-47df-b764-8548d6b2c61b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_zero_extended_value_continuous
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_negative_mark_loss_nonneg
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift9_each_mark_spatial_loss_le
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
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) (hε1 : ε ≤ 1) :
    Integrable (fun yz : ℝ × ℝ => w yz.1 - w (yz.1 + yz.2))
      ((volume.restrict (Ioc (0 : ℝ) ε)).prod (X.ν.restrict (Iio (0 : ℝ)))) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) ε)
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : SFinite ν := levy_negative_jump_measure_sFinite X
  let f : ℝ × ℝ → ℝ := fun yz => w yz.1 - w (yz.1 + yz.2)
  have hcontinuous : Continuous w :=
    avram_route_bv_drift10_zero_extended_value_continuous w hw_cont hw_neg hwzero
  have hfcont : Continuous f :=
    (hcontinuous.comp continuous_fst).sub
      (hcontinuous.comp (continuous_fst.add continuous_snd))
  have hfsm : AEStronglyMeasurable f (μ.prod ν) :=
    hfcont.stronglyMeasurable.aestronglyMeasurable
  have hμ : ∀ z : ℝ, Integrable (fun y => f (y, z)) μ := by
    intro z
    have hzcont : Continuous (fun y : ℝ => f (y, z)) :=
      hcontinuous.sub (hcontinuous.comp (continuous_id.add continuous_const))
    have hcompact : IntegrableOn (fun y : ℝ => f (y, z)) (Icc (0 : ℝ) ε)
        (volume : Measure ℝ) :=
      hzcont.continuousOn.integrableOn_compact isCompact_Icc
    exact hcompact.mono_set Ioc_subset_Icc_self
  have hsecmeas : AEStronglyMeasurable
      (fun z : ℝ => ∫ y, ‖f (y, z)‖ ∂μ) ν :=
    (hfcont.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
  have hweight : Integrable (fun z : ℝ => min ε (-z) * w ε) ν :=
    (avram_route_bv_drift9_original_spatial_truncated_first_moment_L1
      X hBV ε hε hε1).mul_const (w ε)
  have hzmem : ∀ᵐ z ∂ν, z ∈ Iio (0 : ℝ) :=
    ae_restrict_mem measurableSet_Iio
  have hymem : ∀ᵐ y ∂μ, y ∈ Ioc (0 : ℝ) ε :=
    ae_restrict_mem measurableSet_Ioc
  have hinner_nonneg : ∀ᵐ z ∂ν,
      0 ≤ ∫ y, ‖f (y, z)‖ ∂μ :=
    Filter.Eventually.of_forall (fun z => integral_nonneg (fun y => norm_nonneg _))
  have hinner_bound : ∀ᵐ z ∂ν,
      (∫ y, ‖f (y, z)‖ ∂μ) ≤ min ε (-z) * w ε := by
    filter_upwards [hzmem] with z hz
    have heq : (∫ y, ‖f (y, z)‖ ∂μ) = ∫ y, f (y, z) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hymem] with y hy
      have hn := avram_route_bv_drift9_original_negative_mark_loss_nonneg
        C hC w hw_cont hw0 hw_neg hw_smooth hw_grad ε hε hεC y hy z hz
      change ‖w y - w (y + z)‖ = w y - w (y + z)
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
    rw [heq]
    exact avram_route_bv_drift9_each_mark_spatial_loss_le
      C hC w hw_cont hw0 hw_neg hw_smooth hw_grad hwzero ε hε hεC z hz
  have hinner : Integrable (fun z : ℝ => ∫ y, ‖f (y, z)‖ ∂μ) ν :=
    Integrable.mono_nonneg hweight hsecmeas hinner_nonneg hinner_bound
  exact (integrable_prod_iff' hfsm).2
    ⟨Filter.Eventually.of_forall hμ, hinner⟩
