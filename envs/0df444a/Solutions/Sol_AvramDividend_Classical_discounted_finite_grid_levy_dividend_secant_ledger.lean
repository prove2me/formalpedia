-- Prove2me | solution 1 for AvramDividend.Classical.discounted_finite_grid_levy_dividend_secant_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:53:06.339208+00:00
-- url     : https://prove2.me/submissions/177cdfeb-ef14-443d-aa9a-1150717f75db

import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
open AvramDividend.Classical

/-- Discounted finite-grid verification ledger. Each dividend secant is
funded by an uncontrolled Lévy state increment and the initial potential. -/
theorem solution
    (w : ℝ → ℝ) (u preDividend cash : ℕ → ℝ)
    (s : ℕ → ℝ) (q : ℝ) (hs0 : s 0 = 0)
    (hCash : ∀ k : ℕ, cash k ≤ w (preDividend k) - w (u (k + 1)))
    (n : ℕ) :
    (∑ k ∈ Finset.range n, Real.exp (-(q * s (k + 1))) * cash k) +
        Real.exp (-(q * s n)) * w (u n) ≤
      w (u 0) +
        ∑ k ∈ Finset.range n,
          (Real.exp (-(q * s (k + 1))) * w (preDividend k) -
            Real.exp (-(q * s k)) * w (u k)) := by
  induction n with
  | zero => simp [hs0]
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    have h := mul_le_mul_of_nonneg_left (hCash n)
      (le_of_lt (Real.exp_pos (-(q * s (n + 1)))))
    linarith
