-- Prove2me | solution 1 for FamousTheorems.fermat_prime_exponent_power_of_two
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:43:19.712004+00:00
-- url     : https://prove2.me/submissions/7b96c17f-d558-40ca-a4b9-7242c4a53785

import Mathlib

theorem solution {a n : ℕ} (ha : 1 < a) (hn : n ≠ 0) (hp : (a ^ n + 1).Prime) : ∃ m : ℕ, n = 2 ^ m :=
  Nat.pow_of_pow_add_prime ha hn hp
