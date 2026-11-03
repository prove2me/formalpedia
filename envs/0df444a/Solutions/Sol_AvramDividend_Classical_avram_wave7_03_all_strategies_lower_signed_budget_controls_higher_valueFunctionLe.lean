-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_all_strategies_lower_signed_budget_controls_higher_valueFunctionLe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:47:46.476638+00:00
-- url     : https://prove2.me/submissions/686e7345-f343-455a-b25d-bff710913bc6

import Mathlib.Order.CompleteLattice.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_valueFunctionLe_antitone_discount
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_budgets_valueFunctionLe_le
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- A genuine uniform original signed Stieltjes budget at the lower rate
    controls the complete capped value function at every higher rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (B : ℝ)
    (hBudget₁ : ∀ (D : ℝ≥0 → Ω → ℝ)
      (hD : IsAdmissibleLe X x C D) (n : ℕ),
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    valueFunctionLe X q₂ C x ≤ ENNReal.ofReal B := by
  exact (avram_wave7_03_original_valueFunctionLe_antitone_discount
    X x C q₁ q₂ hq).trans
    (avram_wave7_03_original_uniform_signed_budgets_valueFunctionLe_le
      X x C q₁ hq₁ B hBudget₁)
