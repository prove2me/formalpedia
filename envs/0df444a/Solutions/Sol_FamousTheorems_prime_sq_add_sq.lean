-- Prove2me | solution 1 for FamousTheorems.prime_sq_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:36.677557+00:00
-- url     : https://prove2.me/submissions/f9b32ce5-7df4-4c2e-8451-e6ad40a41a15

import Mathlib

theorem solution : ∀ {p : ℕ} [Fact (Nat.Prime p)], p % 4 ≠ 3 → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p :=
  Nat.Prime.sq_add_sq
