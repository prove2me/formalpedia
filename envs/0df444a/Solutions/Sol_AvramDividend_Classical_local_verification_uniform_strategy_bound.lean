-- Prove2me | solution 1 for AvramDividend.Classical.local_verification_uniform_strategy_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:47:19.0914+00:00
-- url     : https://prove2.me/submissions/f91a29b1-4996-441f-bbc2-b3d990a2ef00
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_test_nonneg
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_bv_stochastic_bound
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_ubv_stochastic_bound
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_truncated_bound_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxC : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    dividendValue X q x D ≤ ENNReal.ofReal (w x) := by
  have hComponents :=
    local_verification_hjb_implies_components X q w C hw_hjb
  have hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0 := by
    intro y hy hyC
    obtain ⟨hi, hg, _⟩ := hComponents y hy hyC
    exact ⟨hi, hg⟩
  have hGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y := by
    intro y hy hyC
    exact (hComponents y hy hyC).2.2
  have hNonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω) :=
    local_verification_stochastic_test_nonneg
      X q w C hw_cont hw0 hw_smooth hw_hjb x D hD hxC
  have hMeas : ∀ n : ℕ, Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
    truncated_dividend_payoff_measurable X q x D hD.1.1
  have hTrunc (n : ℕ) :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        ENNReal.ofReal (w x) := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    by_cases hBV : X.BoundedVariation
    · exact admissible_cap_truncated_bv_stochastic_bound
        X hX hBV q hq w C hw_cont hw_neg (hw_smooth.2 hBV)
        hGen hGrad x D hD hNonneg (n : ℝ) hn
    · exact admissible_cap_truncated_ubv_stochastic_bound
        X hX hBV q hq w C hw_cont hw_neg (hw_smooth.1 hBV)
        hGen hGrad x D hD hNonneg (n : ℝ) hn
  exact dividendValue_le_of_truncated_bound_measurable
    X q x D (ENNReal.ofReal (w x)) hMeas hTrunc
