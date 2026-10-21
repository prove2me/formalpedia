-- Prove2me | solution 1 for AvramDividend.Classical.chat04_nat_pairing_rational_grid_coverage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T09:50:54.648096+00:00
-- url     : https://prove2.me/submissions/ddbdd717-d5e5-48d9-b0c4-9121d444e726

import Mathlib.Data.Nat.Pairing
import Mathlib.Data.NNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-!
The Cantor-paired schedule visits every rational reciprocal grid point k/n
with n positive. The construction uses the predecessor of n as its first
pairing coordinate.
-/
theorem solution
    (n k : ℕ) (hn : 0 < n) :
    ∃ j : ℕ,
      ((Nat.unpair j).2 : ℝ≥0) *
        ((((Nat.unpair j).1 + 1 : ℕ) : ℝ≥0)⁻¹) =
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by
  cases n with
  | zero =>
      exact (Nat.not_lt_zero 0 hn).elim
  | succ m =>
      refine ⟨Nat.pair m k, ?_⟩
      simp [Nat.unpair_pair, Nat.succ_eq_add_one]
