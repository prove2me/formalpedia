-- Prove2me | solution 1 for FamousTheorems.euler_beta_integral_gamma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:37:23.12325+00:00
-- url     : https://prove2.me/submissions/885087b9-f513-4502-b5a9-3ed98d290d44

import Mathlib

theorem solution {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    Complex.Gamma s * Complex.Gamma t = Complex.Gamma (s + t) * s.betaIntegral t :=
  Complex.Gamma_mul_Gamma_eq_betaIntegral hs ht
