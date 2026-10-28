-- Prove2me | solution 1 for AvramDividend.Classical.expected_finite_grid_dividend_budget_of_conditional_cash_steps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T18:54:03.083096+00:00
-- url     : https://prove2.me/submissions/3403bd71-b9b8-4d8d-8183-9baaf5dcf45b

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Theorems.Thm_AvramDividend_Classical_expected_finite_grid_dividend_budget_of_conditional_steps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

/-- Telescoping cash budgets where interval payments are conditioned on the past. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (cash V : ℕ → Ω → ℝ)
    (hCashI : ∀ k, Integrable (cash k) P)
    (hVI : ∀ k, Integrable (V k) P)
    (hstep : ∀ k : ℕ, ∀ᵐ ω ∂P,
      (P[(cash k) | 𝓖 k]) ω +
        (P[(V (k + 1)) | 𝓖 k]) ω ≤ V k ω)
    (n : ℕ) :
    (∑ k ∈ Finset.range n, ∫ ω, cash k ω ∂P) +
        ∫ ω, V n ω ∂P ≤
      ∫ ω, V 0 ω ∂P := by
  have hcondI : ∀ k : ℕ,
      Integrable (fun ω => (P[(cash k) | 𝓖 k]) ω) P := by
    intro k
    exact MeasureTheory.integrable_condExp
  have hbudget :=
    AvramDividend.Classical.expected_finite_grid_dividend_budget_of_conditional_steps
      P 𝓖 (fun k ω => (P[(cash k) | 𝓖 k]) ω) V
      hcondI hVI hstep n
  have hcash_eq : ∀ k : ℕ,
      (∫ ω, (P[(cash k) | 𝓖 k]) ω ∂P) =
        ∫ ω, cash k ω ∂P := by
    intro k
    exact MeasureTheory.integral_condExp (𝓖.le k)
  have hsum :
      (∑ k ∈ Finset.range n, ∫ ω, (P[(cash k) | 𝓖 k]) ω ∂P) =
        ∑ k ∈ Finset.range n, ∫ ω, cash k ω ∂P := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hcash_eq k
  rw [hsum] at hbudget
  exact hbudget
