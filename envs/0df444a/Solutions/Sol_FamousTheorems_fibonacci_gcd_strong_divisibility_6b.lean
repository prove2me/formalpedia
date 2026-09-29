-- Prove2me | solution 1 for FamousTheorems.fibonacci_gcd_strong_divisibility_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:25:08.221981+00:00
-- url     : https://prove2.me/submissions/76467710-4419-4609-8548-331a0c556066

import Mathlib

theorem solution (m n : ℕ) : Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n) :=
  Nat.fib_gcd m n
