-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_signed_strict_horizon_expected_to_perpetual_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:07:48.38223+00:00
-- url     : https://prove2.me/submissions/28d6befb-954d-473b-b50a-e366abbaf146

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_signed_expected_to_true_strict_cash_without_extra_finiteness
import Theorems.Thm_AvramDividend_Classical_avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Full original dividendValue from signed finite strict stopped horizon
    budgets with nonnegative prepayment terminal and no vanishing assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (hDStrategy : IsDividendStrategy 𝓕 D)
    (B : ℝ≥0∞)
    (hSignedBudgets : ∀ n : ℕ, ∃ Term : Ω → ℝ,
      (∀ᵐ ω ∂P, 0 ≤ Term ω) ∧
      (∫⁻ ω, ENNReal.ofReal
        (((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
          Iio (((n + 1 : ℕ) : ℝ)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω)).toReal) + Term ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by
  apply avram_limit2_uniform_strict_horizon_cash_plus_terminal_budget_to_value
    X q x D hD B
  intro n
  obtain ⟨Term, hPos, hMean⟩ := hSignedBudgets n
  refine ⟨(fun ω => ENNReal.ofReal (Term ω)), ?_⟩
  have hT : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by positivity
  exact avram_limit2_original_signed_expected_to_true_strict_cash_without_extra_finiteness
    X q hq x D hDStrategy (((n + 1 : ℕ) : ℝ)) hT
    Term B hPos hMean
