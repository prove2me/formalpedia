-- Prove2me | solution 1 for FamousTheorems.chebyshev_orthogonality_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:46:27.694388+00:00
-- url     : https://prove2.me/submissions/e689972e-7133-4ec4-9b62-6ef694249589

import Mathlib

theorem solution {n m : ℕ} (h : n ≠ m) :
    ∫ x, (Polynomial.Chebyshev.T ℝ n).eval x * (Polynomial.Chebyshev.T ℝ m).eval x
      ∂Polynomial.Chebyshev.measureT = 0 :=
  Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne h
