-- Prove2me | solution 1 for FamousTheorems.abel_x_pow_prime_sub_irreducible_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:01:40.680443+00:00
-- url     : https://prove2.me/submissions/b6705f9f-1beb-4b98-8bc8-043ec745ab88

import Mathlib

theorem solution {K : Type*} [Field K] {p : ℕ} (hp : p.Prime) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (Polynomial.X ^ p - Polynomial.C a) :=
  X_pow_sub_C_irreducible_of_prime hp ha
