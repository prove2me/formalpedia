-- Prove2me | solution 1 for CircuitLowerBound.SmallFacts.pack_lt
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:45:56.975196+00:00
-- url     : https://prove2.me/submissions/62c3ab7e-1b37-4393-81e6-3d79550c9826

import Mathlib.Tactic

set_option autoImplicit false

theorem solution {x y A M : ℕ} (hx : x < A) (hy : y < M) : x * M + y < A * M := by
  have h : (x + 1) * M ≤ A * M := Nat.mul_le_mul_right M (Nat.succ_le_of_lt hx)
  nlinarith
