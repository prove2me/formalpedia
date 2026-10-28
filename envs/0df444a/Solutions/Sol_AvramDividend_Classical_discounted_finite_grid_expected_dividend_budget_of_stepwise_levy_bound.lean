-- Prove2me | solution 1 for AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_stepwise_levy_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:31:29.106367+00:00
-- url     : https://prove2.me/submissions/f9a56377-e84f-40a1-9b19-62ae23c4ffdb

import Mathlib.Data.Finset.Range
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_expected_finite_grid_levy_residual_nonpositive_of_step_bounds
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_expected_dividend_budget_of_levy_residual

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Finset
open AvramDividend.Classical

/-- A nonpositive expected Lévy generator increment at every stopped-grid
step yields the expected discounted dividend budget at every horizon. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (u preDividend cash : ℕ → Ω → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0) (x : ℝ)
    (hu0 : ∀ ω, u 0 ω = x)
    (hCash : ∀ k ω, cash k ω ≤ w (preDividend k ω) - w (u (k + 1) ω))
    (n : ℕ)
    (hCashInt : Integrable (fun ω =>
      ∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k ω) P)
    (hTerminalInt : Integrable (fun ω =>
      Real.exp (-(q * s n)) * w (u n ω)) P)
    (hStepInt : ∀ k, Integrable (fun ω =>
      Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
        Real.exp (-(q * s k)) * w (u k ω)) P)
    (hStep : ∀ k, (∫ ω,
      Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
        Real.exp (-(q * s k)) * w (u k ω) ∂P) ≤ 0)
    (hTerminal : 0 ≤
      ∫ ω, Real.exp (-(q * s n)) * w (u n ω) ∂P) :
    (∫ ω, ∑ k ∈ Finset.range n,
      Real.exp (-(q * s (k + 1))) * cash k ω ∂P) ≤ w x := by
  have hResidualInt : Integrable (fun ω =>
      ∑ k ∈ Finset.range n,
        (Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
          Real.exp (-(q * s k)) * w (u k ω))) P := by
    apply integrable_finset_sum
    intro k hk
    exact hStepInt k
  have hResidual : (∫ ω, ∑ k ∈ Finset.range n,
      (Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
        Real.exp (-(q * s k)) * w (u k ω)) ∂P) ≤ 0 :=
    AvramDividend.Classical.expected_finite_grid_levy_residual_nonpositive_of_step_bounds
      (fun k ω =>
        Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
          Real.exp (-(q * s k)) * w (u k ω))
      hStepInt hStep n
  exact AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_levy_residual
    w u preDividend cash s q hs0 x hu0 hCash n
    hCashInt hTerminalInt hResidualInt hResidual hTerminal
