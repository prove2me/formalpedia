-- Prove2me | solution 1 for FamousTheorems.gcd_eq_gcd_ab
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:58.909588+00:00
-- url     : https://prove2.me/submissions/c1ca0278-cd0f-465b-b08b-098c50426d1d

import Mathlib

theorem solution : ∀ x y : ℕ, (Nat.gcd x y : ℤ) = x * Nat.gcdA x y + y * Nat.gcdB x y :=
  Nat.gcd_eq_gcd_ab
