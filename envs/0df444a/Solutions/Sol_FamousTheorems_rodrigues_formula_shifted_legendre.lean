-- Prove2me | solution 1 for FamousTheorems.rodrigues_formula_shifted_legendre
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:00:07.389987+00:00
-- url     : https://prove2.me/submissions/e9409ef9-0c9c-4706-9d0a-63a680d81bdb

import Mathlib

theorem solution (n : ℕ) : (n.factorial : Polynomial ℤ) * Polynomial.shiftedLegendre n =
    Polynomial.derivative^[n] (Polynomial.X ^ n * (1 - Polynomial.X) ^ n) :=
  Polynomial.factorial_mul_shiftedLegendre_eq n
