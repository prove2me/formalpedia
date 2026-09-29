-- Prove2me | solution 1 for FamousTheorems.exists_infinite_primes
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:36.677334+00:00
-- url     : https://prove2.me/submissions/a382a79f-2290-433f-a9d8-a587d4981c5e

import Mathlib

theorem solution : ∀ n : ℕ, ∃ p, n ≤ p ∧ Nat.Prime p :=
  Nat.exists_infinite_primes
