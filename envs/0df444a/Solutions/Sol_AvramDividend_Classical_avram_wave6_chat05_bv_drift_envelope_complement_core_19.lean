-- Prove2me | solution 19 for AvramDividend.Classical.avram_wave6_chat05_bv_drift_envelope_complement_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:05:07.740183+00:00
-- url     : https://prove2.me/submissions/cddd5401-66d0-42b1-9597-822da8c034ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn51_hjb_positive_of_positive_drift
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_signed_fatou_grids_to_closed_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive BV drift and the source HJB exclude a zero initial benchmark;
    the positive physical Fatou branch then closes the original envelope. -/
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
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : ¬ (x + T * X.drift ≤ w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hSharp :=
    avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
      X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_grad
      x hx hxc D hD T hT hEnvelope
  have hwpos := avram_bv_env3_turn51_hjb_positive_of_positive_drift
    X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
    hw_grad x hx hxc hSharp.2.1
  obtain ⟨F, M, B, hFm, hFi, hFn, hR, hBound, hFatou⟩ :=
    avram_p3_grid4_original_positive_benchmark_signed_fatou_from_physical_source
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc hwpos D hD hw_nonneg hjump T hT hSharp.1
  exact avram_bv_env3_original_signed_fatou_grids_to_closed_cash
    X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    x hx hxc D hD hw_nonneg hjump T hT hSharp.1 F M B
    hFm hFi hFn hR hBound hFatou
