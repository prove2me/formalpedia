-- Prove2me | solution 1 for FamousTheorems.chebyshev_polynomial_cos
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:58:44.342008+00:00
-- url     : https://prove2.me/submissions/186d3191-96f5-4836-98c2-9b22b97934ab

import Mathlib

theorem solution (θ : ℂ) (n : ℤ) : (Polynomial.Chebyshev.T ℂ n).eval (Complex.cos θ) = Complex.cos (n * θ) :=
  Polynomial.Chebyshev.T_complex_cos θ n
