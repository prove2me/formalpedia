-- Prove2me | solution 1 for AvramDividend.Classical.discounted_finite_grid_expected_dividend_budget_of_levy_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:26:44.167299+00:00
-- url     : https://prove2.me/submissions/ba63568a-65a6-4609-baa7-7eb5b8633d56

import Mathlib.Data.Finset.Range
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_discounted_finite_grid_levy_dividend_secant_ledger

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Finset
open AvramDividend.Classical

/-- Integrate the pathwise Lévy dividend ledger and dispose of the expected
signed Lévy residual and the expected terminal verification value. -/
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
    (hResidualInt : Integrable (fun ω =>
      ∑ k ∈ Finset.range n,
        (Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
          Real.exp (-(q * s k)) * w (u k ω))) P)
    (hResidual : (∫ ω, ∑ k ∈ Finset.range n,
      (Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
        Real.exp (-(q * s k)) * w (u k ω)) ∂P) ≤ 0)
    (hTerminal : 0 ≤
      ∫ ω, Real.exp (-(q * s n)) * w (u n ω) ∂P) :
    (∫ ω, ∑ k ∈ Finset.range n,
      Real.exp (-(q * s (k + 1))) * cash k ω ∂P) ≤ w x := by
  have hpoint : ∀ ω,
      (∑ k ∈ Finset.range n,
        Real.exp (-(q * s (k + 1))) * cash k ω) +
        Real.exp (-(q * s n)) * w (u n ω) ≤
      w x + ∑ k ∈ Finset.range n,
        (Real.exp (-(q * s (k + 1))) * w (preDividend k ω) -
          Real.exp (-(q * s k)) * w (u k ω)) := by
    intro ω
    simpa only [hu0 ω] using
      (AvramDividend.Classical.discounted_finite_grid_levy_dividend_secant_ledger
        w (fun k => u k ω) (fun k => preDividend k ω)
        (fun k => cash k ω) s q hs0 (fun k => hCash k ω) n)
  have hmono := integral_mono
    (hCashInt.add hTerminalInt)
    ((integrable_const (w x)).add hResidualInt)
    hpoint
  simp only [Pi.add_apply] at hmono
  rw [integral_add hCashInt hTerminalInt,
    integral_add (integrable_const (w x)) hResidualInt] at hmono
  have hconst : (∫ _ : Ω, w x ∂P) = w x := by simp
  rw [hconst] at hmono
  linarith only [hmono, hResidual, hTerminal]
