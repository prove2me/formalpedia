-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_uniform_lower_discount_signed_budget_controls_higher_dividendValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:47:48.491772+00:00
-- url     : https://prove2.me/submissions/4df3208a-8fa5-4a02-bdbd-e8b209f4f608

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A genuine original signed Stieltjes horizon budget at a lower discount
    controls every higher-rate full ENNReal source dividendValue. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (B : ℝ)
    (hBudget₁ : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    dividendValue X q₂ x D ≤ ENNReal.ofReal B := by
  exact (avram_wave7_03_original_dividendValue_antitone_discount
    X x D q₁ q₂ hq).trans
    (avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
      X x C D hD q₁ hq₁ B hBudget₁)
