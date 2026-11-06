-- Prove2me | solution 9 for AvramDividend.Classical.avram_wave6_chat05_bv_drift_envelope_complement_core
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:01:45.754268+00:00
-- url     : https://prove2.me/submissions/b5fdbf23-5464-4edc-b62a-a59192e1b474
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_integration_p3_original_strict_source_martingale_drift_split
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_any_clock_strict_signed_to_full_cash
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

  classical
  let S : ℝ≥0 := ⟨T, hT⟩
  have hTpos := (avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
    X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_grad
    x hx hxc D hD T hT hEnvelope).1
  obtain ⟨M, B, ⟨hMI, hMzero⟩, ⟨hBI, hBnonpos⟩, hPath⟩ :=
    avram_integration_p3_original_strict_source_martingale_drift_split
      X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hw_gen
      hw_grad x hx hxc D hD hw_nonneg hjump T hT hTpos
  have hSigned : (∫ ω, M ω + B ω ∂P) ≤ 0 := by
    rw [integral_add hMI hBI, hMzero]
    simpa only [zero_add] using hBnonpos
  have hWitness : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D ⟨T, hT⟩ ω)
       else 0) ≤ w x + M ω + B ω := by
    filter_upwards [hPath] with ω hω
    simpa only [S] using hω
  exact avram_bv_env3_original_any_clock_strict_signed_to_full_cash
    X hBV q (le_of_lt hq) w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
    x hx hxc D hD T hT hTpos M B hMI hBI hSigned hWitness
