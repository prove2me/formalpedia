-- Prove2me | solution 1 for AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_HJB_gradient_and_step_generator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:42:49.396003+00:00
-- url     : https://prove2.me/submissions/fbca3b62-166f-42d2-92de-55f58300538c

import Mathlib.Data.Finset.Range
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_expected_dividend_budget_of_stepwise_levy_bound
import Theorems.Thm_AvramDividend_Classical_dividend_jump_drop_le_verification_drop_of_gradient

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Finset Set
open AvramDividend.Classical

/-- The HJB derivative inequality controls grid dividends, while each
nonpositive Lévy generator residual controls the expected stochastic gain. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℝ → ℝ) (u preDividend cash : ℕ → Ω → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0) (x : ℝ)
    (hu0 : ∀ ω, u 0 ω = x)
    (hAfter : ∀ k ω, u (k + 1) ω = preDividend k ω - cash k ω)
    (hCashNonneg : ∀ k ω, 0 ≤ cash k ω)
    (hwCont : ∀ k ω, ContinuousOn w
      (Icc (preDividend k ω - cash k ω) (preDividend k ω)))
    (hwDiff : ∀ k ω, DifferentiableOn ℝ w
      (interior (Icc (preDividend k ω - cash k ω) (preDividend k ω))))
    (hwGrad : ∀ k ω, ∀ y ∈
      interior (Icc (preDividend k ω - cash k ω) (preDividend k ω)),
        1 ≤ deriv w y)
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
  have hCash : ∀ k ω, cash k ω ≤
      w (preDividend k ω) - w (u (k + 1) ω) := by
    intro k ω
    rw [hAfter k ω]
    exact AvramDividend.Classical.dividend_jump_drop_le_verification_drop_of_gradient
      w (preDividend k ω) (cash k ω)
      (hCashNonneg k ω) (hwCont k ω) (hwDiff k ω) (hwGrad k ω)
  exact AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_stepwise_levy_bound
    w u preDividend cash s q hs0 x hu0 hCash n
    hCashInt hTerminalInt hStepInt hStep hTerminal
