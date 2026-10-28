-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_real_cash_prefixes_nonnegative_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T20:24:41.07855+00:00
-- url     : https://prove2.me/submissions/1419c0ab-c624-4b59-a871-82739441f417

import Mathlib.Data.ENNReal.Real
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Range

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

/-- Nonnegative real Stieltjes unit cash gives nonnegative prefixes and
    an increasing ENNReal-embedded cash sequence for monotone convergence. -/
theorem solution
    (cash : ℕ → ℝ) (hCashNN : ∀ k, 0 ≤ cash k) :
    (∀ n : ℕ, 0 ≤ ∑ k ∈ Finset.range n, cash k) ∧
    Monotone (fun n : ℕ =>
      ENNReal.ofReal (∑ k ∈ Finset.range n, cash k)) := by
  constructor
  · intro n
    exact Finset.sum_nonneg (by intro k hk; exact hCashNN k)
  · apply monotone_nat_of_le_succ
    intro n
    apply ENNReal.ofReal_le_ofReal
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (hCashNN n)
