-- Prove2me | solution 1 for FamousTheorems.jacobi_theta_two_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:18:18.777387+00:00
-- url     : https://prove2.me/submissions/772ffce5-f7f6-4fbe-9613-acbeb7f187e0

import Mathlib

theorem solution (z τ : ℂ) :
    jacobiTheta₂ z τ = 1 / (-Complex.I * τ) ^ (1 / 2 : ℂ) * Complex.exp (-(Real.pi : ℂ) * Complex.I * z ^ 2 / τ) *
      jacobiTheta₂ (z / τ) (-1 / τ) :=
  jacobiTheta₂_functional_equation z τ
