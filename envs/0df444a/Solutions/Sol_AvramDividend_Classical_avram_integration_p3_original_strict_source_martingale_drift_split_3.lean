-- Prove2me | solution 3 for AvramDividend.Classical.avram_integration_p3_original_strict_source_martingale_drift_split
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T15:57:17.833071+00:00
-- url     : https://prove2.me/submissions/7d122bcc-28aa-4c09-a3b6-5e208e943b48
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_integration_p3_original_stopped_triple_mesh_source_certificate
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_triple_mesh_stopped_signed_witness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

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
    ∃ M B : Ω → ℝ,
      (Integrable M P ∧ (∫ ω, M ω ∂P) = 0) ∧
      (Integrable B P ∧ (∫ ω, B ω ∂P) ≤ 0) ∧
      (∀ᵐ ω ∂P,
        let S : ℝ≥0 := ⟨T, hT⟩
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
          (if (S : ℝ≥0∞) < ruinTime X x D ω then
            Real.exp (-(q * T)) * w (riskProcess X x D S ω)
          else 0) ≤ w x + M ω + B ω) := by
  let Y : Ω → ℝ := fun ω =>
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
  obtain ⟨Ymesh, Mmesh, Bmesh, M, B, DM, DB,
      hMMeas, hBMeas, hDM, hDB, hMDom, hBDom,
      hYLim, hMLim, hBLim, hMMean, hBMean, hMesh⟩ :=
    AvramDividend.Classical.avram_integration_p3_original_stopped_triple_mesh_source_certificate
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen hw_grad
      x hx hxc D hD hw_nonneg hjump T hT hTpos
  exact AvramDividend.Classical.avram_p3_bv_original_triple_mesh_stopped_signed_witness
    P Ymesh Mmesh Bmesh Y M B DM DB (w x)
    hMMeas hBMeas hDM hDB hMDom hBDom hYLim hMLim hBLim hMMean hBMean hMesh
