-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_chronological_descFactorial_step_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:43:49.774417+00:00
-- url     : https://prove2.me/submissions/22a847ea-2b9d-4053-b2c5-7c7c38d6f19a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Nat
noncomputable section

/-- Each new physical jump contributes one more chronological factorial tuple. -/
theorem solution (k n : ℕ) :
    Nat.descFactorial (k + 1) (n + 1) =
      Nat.descFactorial k (n + 1) + (n + 1) * Nat.descFactorial k n := by
  rw [Nat.succ_descFactorial_succ, Nat.descFactorial_succ]
  by_cases hn : n ≤ k
  · have hs : k - n + (n + 1) = k + 1 := by omega
    calc
      (k + 1) * k.descFactorial n =
          ((k - n) + (n + 1)) * k.descFactorial n := by rw [hs]
      _ = (k - n) * k.descFactorial n + (n + 1) * k.descFactorial n := by ring
  · have hk : k < n := Nat.lt_of_not_ge hn
    simp [Nat.descFactorial_eq_zero_iff_lt.mpr hk]
