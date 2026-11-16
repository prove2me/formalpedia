-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_nat_count_occupancy_factorial_sandwich_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:51:16.797605+00:00
-- url     : https://prove2.me/submissions/b07f87f8-2a0a-48c4-888e-9c5999a651ca

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- Occupancy of an integer count is bounded by its two factorial moments. -/
theorem solution (k : ℕ) :
    (k : ℝ) - ((k : ℝ) * ((k : ℝ) - 1)) / 2 ≤
        (if k = 0 then (0 : ℝ) else 1) ∧
      (if k = 0 then (0 : ℝ) else 1) ≤ (k : ℝ) := by
  cases k with
  | zero => norm_num
  | succ k =>
      cases k with
      | zero => norm_num
      | succ k =>
          simp only [Nat.succ_ne_zero, ite_false]
          have hNat : 2 ≤ Nat.succ (Nat.succ k) := by omega
          have hk : (2 : ℝ) ≤ (Nat.succ (Nat.succ k) : ℝ) :=
            by exact_mod_cast hNat
          have hprod : 0 ≤
              ((Nat.succ (Nat.succ k) : ℝ) - 1) *
                ((Nat.succ (Nat.succ k) : ℝ) - 2) :=
            mul_nonneg (by linarith) (by linarith)
          constructor
          · nlinarith [hprod]
          · linarith
