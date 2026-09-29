-- Prove2me | solution 1 for FamousTheorems.euler_formula_exp_i_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:25:42.193729+00:00
-- url     : https://prove2.me/submissions/873b6925-d7dd-4b69-9800-f1f591581f3a

import Mathlib

theorem solution (x : ℂ) : Complex.exp (x * Complex.I) = Complex.cos x + Complex.sin x * Complex.I :=
  Complex.exp_mul_I x
