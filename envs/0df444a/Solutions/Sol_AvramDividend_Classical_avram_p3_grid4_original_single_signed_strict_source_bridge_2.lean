-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_grid4_original_single_signed_strict_source_bridge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:43:13.2802+00:00
-- url     : https://prove2.me/submissions/a2fd2d65-9dc4-4b97-ab76-fea2e6fbfdab
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_original_stopped_signed_single_residual_mesh
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_mesh_residual_integrable_limit
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_dominated_mesh_residual_mean_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    ∃ Z : Ω → ℝ,
      Integrable Z P ∧ (∫ ω, Z ω ∂P) ≤ 0 ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal +
        (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0) ≤ w x + Z ω) := by
  obtain ⟨Ymesh, Zmesh, Z, DZ, hZM, hDZ, hDom, hYLim, hZLim,
    hMean, hBudget⟩ :=
    avram_a19_original_stopped_signed_single_residual_mesh
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hTpos
  refine ⟨Z, ?_, ?_, ?_⟩
  · exact avram_p3_c_bvchain_dominated_mesh_residual_integrable_limit
      P Zmesh Z DZ hZM hDZ hDom hZLim
  · exact avram_p3_c_bvchain_dominated_mesh_residual_mean_nonpos
      P Zmesh Z DZ hZM hDZ hDom hZLim hMean
  · filter_upwards [hYLim, hZLim, hBudget] with ω hy hz hb
    have hBoundLim : Tendsto (fun n => w x + Zmesh n ω)
        atTop (nhds (w x + Z ω)) := tendsto_const_nhds.add hz
    exact le_of_tendsto_of_tendsto hy hBoundLim
      (Filter.Eventually.of_forall hb)
