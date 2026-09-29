-- Prove2me | solution 1 for FamousTheorems.euler_reflection_formula
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:03:01.785378+00:00
-- url     : https://prove2.me/submissions/d58e360c-753c-419c-a93d-1a68822938e6

import Mathlib

theorem solution (z : ℂ) : Complex.Gamma z * Complex.Gamma (1 - z) = Real.pi / Complex.sin (Real.pi * z) :=
  Complex.Gamma_mul_Gamma_one_sub z
