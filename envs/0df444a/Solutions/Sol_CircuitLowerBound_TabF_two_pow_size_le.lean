-- Prove2me | solution 1 for CircuitLowerBound.TabF.two_pow_size_le
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:28:40.079202+00:00
-- url     : https://prove2.me/submissions/521f3d58-8f01-4a4c-b96e-5e11fff9d7e3

import Mathlib.Data.Nat.Size
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by
  cases h : Nat.size n with
  | zero => simp [h]
  | succ k =>
      have hk : k < Nat.size n := by omega
      have hpow : 2 ^ k ≤ n := Nat.lt_size.mp hk
      rw [Nat.pow_succ]
      omega
