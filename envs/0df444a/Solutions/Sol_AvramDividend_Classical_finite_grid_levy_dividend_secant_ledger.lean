-- Prove2me | solution 1 for AvramDividend.Classical.finite_grid_levy_dividend_secant_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:53:02.090519+00:00
-- url     : https://prove2.me/submissions/bab44d4b-9827-4d2b-b2d8-9c70fc880c1a

import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
open AvramDividend.Classical

/-- Pathwise finite-grid balance: dividend secants are funded by the
initial verification value and the cumulative uncontrolled state increments. -/
theorem solution
    (w : ℝ → ℝ) (u preDividend cash : ℕ → ℝ)
    (hCash : ∀ k : ℕ, cash k ≤ w (preDividend k) - w (u (k + 1)))
    (n : ℕ) :
    (∑ k ∈ Finset.range n, cash k) + w (u n) ≤
      w (u 0) + ∑ k ∈ Finset.range n, (w (preDividend k) - w (u k)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    have h := hCash n
    linarith
