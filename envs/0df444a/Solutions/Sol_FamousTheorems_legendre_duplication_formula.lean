-- Prove2me | solution 1 for FamousTheorems.legendre_duplication_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:03:29.877042+00:00
-- url     : https://prove2.me/submissions/ae206466-02ce-4a62-990a-ec9f34810f85

import Mathlib

theorem solution (s : ℂ) : Complex.Gamma s * Complex.Gamma (s + 1 / 2) = Complex.Gamma (2 * s) * 2 ^ (1 - 2 * s) * (Real.sqrt Real.pi : ℂ) :=
  Complex.Gamma_mul_Gamma_add_half s
