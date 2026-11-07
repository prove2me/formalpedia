-- Prove2me | solution 10 for AvramDividend.Classical.avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:10:54.656937+00:00
-- url     : https://prove2.me/submissions/0e89f6d8-11d3-48e8-be90-fb2b5446e9fa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_original_stopped_signed_single_residual_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_mesh_residual_integrable_limit
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_mesh_residual_mean_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_single_signed_budget_to_fatou_certificate
import Theorems.Thm_AvramDividend_Classical_avram_limit1_p3_original_signed_grid_witness_to_strict_real_prebudget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Independent dominated original stopped-mesh reduction for the canonical BV HJB prebudget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by
  obtain ⟨Ymesh, Zmesh, Z, DZ, hZMeas, hDZ, hZDom, hYLim, hZLim,
    hZMean, hBudget⟩ :=
    avram_a19_original_stopped_signed_single_residual_mesh
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  have hZInt := avram_p3_c_bvchain_dominated_mesh_residual_integrable_limit
    P Zmesh Z DZ hZMeas hDZ hZDom hZLim
  have hZNonpos := avram_p3_c_bvchain_dominated_mesh_residual_mean_nonpos
    P Zmesh Z DZ hZMeas hDZ hZDom hZLim hZMean
  have hPath : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ≤ w x + Z ω := by
    filter_upwards [hYLim, hZLim, hBudget] with ω hYω hZω hBoundω
    have hR : Tendsto (fun n => w x + Zmesh n ω) atTop
        (nhds (w x + Z ω)) := tendsto_const_nhds.add hZω
    exact le_of_tendsto_of_tendsto hYω hR
      (Filter.Eventually.of_forall hBoundω)
  have hFatou := avram_p3_grid3_original_single_signed_budget_to_fatou_certificate
    X hBV q hq w C hw_cont hw_neg x D hD hw_nonneg
    T hT hTpos Z hZInt hZNonpos hPath
  exact avram_limit1_p3_original_signed_grid_witness_to_strict_real_prebudget
    X hBV x C D hD w hw_cont hw_neg hw_nonneg q (le_of_lt hq)
    T hT hTpos hFatou
