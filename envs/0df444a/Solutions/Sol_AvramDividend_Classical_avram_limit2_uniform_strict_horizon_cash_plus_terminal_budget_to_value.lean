-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T11:11:36.797871+00:00
-- url     : https://prove2.me/submissions/1af048ec-aa4b-468c-8cfc-93d34247f6d3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Uniform strictly positive stopped cash-plus-terminal ENNReal budgets
    control the original perpetual dividend value without terminal vanishing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞)
    (hBudget : ∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by
  rw [dividendValue_eq_iSup_truncated X q x D hD]
  refine iSup_le fun n => ?_
  obtain ⟨Terminal, hBudgetN⟩ := hBudget n
  have hCast : (n : ℝ) < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.lt_succ_self n
  have hClosedToStrict :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := by
    apply lintegral_mono
    intro ω
    apply lintegral_mono_set
    intro t ht
    exact ⟨ht.1, lt_of_le_of_lt ht.2 hCast⟩
  have hStrictToBudget :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iio (((n + 1 : ℕ) : ℝ)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) := by
    apply lintegral_mono
    intro ω
    exact le_add_of_nonneg_right bot_le
  exact hClosedToStrict.trans (hStrictToBudget.trans hBudgetN)
