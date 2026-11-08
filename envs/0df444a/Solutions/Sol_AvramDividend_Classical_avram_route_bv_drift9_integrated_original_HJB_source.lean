-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_bv_drift9_integrated_original_HJB_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T15:01:07.114271+00:00
-- url     : https://prove2.me/submissions/4efc5738-6c2f-4e94-9960-fc23083fce33

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_original_spatial_jump_product_L1
import Theorems.Thm_AvramDividend_Classical_avram_route_bv_drift10_zero_extended_value_continuous
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
    (hw_smooth : ContDiffOn ℝ 1 w {y | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hwzero : w 0 = 0) (ε : ℝ) (hε : 0 < ε)
    (hεC : ENNReal.ofReal ε < C) (hε1 : ε ≤ 1) :
    X.drift * w ε ≤ ∫ y in Ioc (0 : ℝ) ε,
      (q * w y - ∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν)
      ∂(volume : Measure ℝ) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) ε)
  let ν : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  letI : SFinite ν := levy_negative_jump_measure_sFinite X
  have hcont : ContinuousOn w (Icc (0 : ℝ) ε) := hw_cont.mono (by intro y hy; exact hy.1)
  have hsub : interior (Icc (0 : ℝ) ε) ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    have hi : y ∈ Ioo (0 : ℝ) ε := by simpa only [interior_Icc] using hy
    have he := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hi.1.le).2 hi.2
    exact ⟨hi.1, he.trans hεC⟩
  have hdiffer : DifferentiableOn ℝ w (interior (Icc (0 : ℝ) ε)) := hw_smooth.differentiableOn_one.mono hsub
  have hderiv : ∀ y ∈ Ioo (0 : ℝ) ε, HasDerivAt w (deriv w y) y := by
    intro y hy
    exact (hdiffer.differentiableAt (isOpen_interior.mem_nhds
      (by simpa only [interior_Icc] using hy))).hasDerivAt
  have hpos : ∀ y ∈ Ioo (0 : ℝ) ε, 0 ≤ deriv w y := by
    intro y hy
    have he := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hy.1.le).2 hy.2
    linarith [hw_grad y hy.1 (he.trans hεC)]
  have hint : IntegrableOn (deriv w) (Ioc (0 : ℝ) ε) volume :=
    intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hpos
  have hFTC : (∫ y in Ioc (0 : ℝ) ε, deriv w y ∂volume) = w ε := by
    have hucont : ContinuousOn w (uIcc (0 : ℝ) ε) := by
      simpa [uIcc_of_le hε.le] using hcont
    have hf := intervalIntegral.integral_deriv_eq_sub_uIoo hucont
      (by intro y hy; exact (hderiv y (by simpa [Set.uIoo, hε.le] using hy)).differentiableAt)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hε.le).2 hint)
    simpa [intervalIntegral.integral_of_le hε.le, hwzero] using hf
  have hqI : Integrable (fun y : ℝ => q * w y) μ := by
    have hc : Continuous (fun y : ℝ => q * w y) :=
      continuous_const.mul (avram_route_bv_drift10_zero_extended_value_continuous
        w hw_cont hw_neg hwzero)
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hJ : Integrable (fun y : ℝ => ∫ z, w y - w (y + z) ∂ν) μ :=
    (avram_route_bv_drift10_original_spatial_jump_product_L1
      X hBV w C hC hw_cont hw0 hw_neg hw_smooth hw_grad hwzero ε hε hεC hε1).integral_prod_left
  have hp (y : ℝ) : q * w y - (∫ z, w (y + z) - w y ∂ν) =
      q * w y + ∫ z, w y - w (y + z) ∂ν := by
    have hn : (fun z : ℝ => w (y + z) - w y) = fun z => -(w y - w (y + z)) := by funext z; ring
    rw [hn, integral_neg]; ring
  have hR : Integrable (fun y : ℝ => q * w y - ∫ z, w (y + z) - w y ∂ν) μ := by
    have hf : (fun y : ℝ => q * w y - ∫ z, w (y + z) - w y ∂ν) =
        (fun y => q * w y + ∫ z, w y - w (y + z) ∂ν) := by
      funext y; exact hp y
    rw [hf]
    exact hqI.add hJ
  have hm : ∀ᵐ y ∂μ, X.drift * deriv w y ≤
      q * w y - ∫ z, w (y + z) - w y ∂ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    have he := ENNReal.ofReal_le_ofReal hy.2
    have hg := hw_gen y hy.1 (lt_of_le_of_lt he hεC)
    have hv := hg.2
    rw [boundedVariation_generator_physical_drift_representation X hBV w y hg.1] at hv
    linarith
  have hi : Integrable (fun y : ℝ => X.drift * deriv w y) μ := hint.const_mul _
  calc
    X.drift * w ε = ∫ y, X.drift * deriv w y ∂μ := by
      rw [integral_const_mul]; exact congrArg (fun t : ℝ => X.drift * t) hFTC.symm
    _ ≤ ∫ y, q * w y - ∫ z, w (y + z) - w y ∂ν ∂μ :=
      integral_mono_ae hi hR hm
