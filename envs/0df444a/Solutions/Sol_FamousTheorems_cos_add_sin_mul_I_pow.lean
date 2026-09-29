-- Prove2me | solution 1 for FamousTheorems.cos_add_sin_mul_I_pow
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:17:24.722308+00:00
-- url     : https://prove2.me/submissions/9ab09e17-bdb7-4e75-bca1-918db8ff0549

import Mathlib

theorem solution : ∀ (n : ℕ) (z : ℂ), (Complex.cos z + Complex.sin z * Complex.I) ^ n =
    Complex.cos (n * z) + Complex.sin (n * z) * Complex.I :=
  Complex.cos_add_sin_mul_I_pow
