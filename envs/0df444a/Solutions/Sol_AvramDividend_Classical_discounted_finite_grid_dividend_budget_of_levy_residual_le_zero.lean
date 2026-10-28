-- Prove2me | solution 1 for AvramDividend.Classical.discounted_finite_grid_dividend_budget_of_levy_residual_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:02:04.085883+00:00
-- url     : https://prove2.me/submissions/b8f9d751-5b21-4d80-89a8-d57868358267

import Mathlib.Data.Finset.Range
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_levy_dividend_secant_ledger

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
open AvramDividend.Classical

/-- A nonpositive Lévy residual and a nonnegative terminal value close
the discounted finite-grid stochastic dividend budget. -/
theorem solution
    (w : ℝ → ℝ) (u preDividend cash : ℕ → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0)
    (hCash : ∀ k : ℕ, cash k ≤ w (preDividend k) - w (u (k + 1)))
    (n : ℕ)
    (hResidual : (∑ k ∈ Finset.range n,
      (Real.exp (-(q * s (k + 1))) * w (preDividend k) -
        Real.exp (-(q * s k)) * w (u k))) ≤ 0)
    (hTerminal : 0 ≤ w (u n)) :
    (∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k) ≤
      w (u 0) := by
  have hledger :=
    AvramDividend.Classical.discounted_finite_grid_levy_dividend_secant_ledger
      w u preDividend cash s q hs0 hCash n
  have hterm :
      0 ≤ Real.exp (-(q * s n)) * w (u n) :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) hTerminal
  linarith
