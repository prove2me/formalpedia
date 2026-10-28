-- Prove2me | solution 1 for AvramDividend.Classical.capped_hjb_actual_dividend_le_derivative_weighted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:35:19.395004+00:00
-- url     : https://prove2.me/submissions/4d53cc27-6e4e-4b45-a184-741df8d84cf8

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_actual_dividend_le_derivative_weighted
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- On any actual stopped dividend payment window lying in the strictly positive reserve interior below a cap, the HJB maximum equation forces the candidate derivative to be at least one. Therefore the actual discounted real Stieltjes payout is at most the derivative-weighted payout, provided that the latter is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) (u : ℝ → ℝ)
    (hregion : ∀ t ∈ paymentTimes σ ∩ Iic (T : ℝ),
      0 < u t ∧ ENNReal.ofReal (u t) < C)
    (hWeighted : IntegrableOn (fun t : ℝ =>
      Real.exp (-(q * t)) * deriv w (u t))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω)) :
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤
    (∫ t in paymentTimes σ ∩ Iic (T : ℝ),
      Real.exp (-(q * t)) * deriv w (u t) ∂(dividendMeasure D ω)) := by
  apply discounted_actual_dividend_le_derivative_weighted
    D hD q hq σ T ω w u
  · intro t ht
    obtain ⟨ht0, htC⟩ := hregion t ht
    obtain ⟨_, _, hderiv⟩ :=
      hjb_component_inequalities X q w C hw_hjb (u t) ht0 htC
    exact hderiv
  · exact hWeighted
