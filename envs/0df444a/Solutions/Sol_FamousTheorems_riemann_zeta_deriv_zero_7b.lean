-- Prove2me | solution 1 for FamousTheorems.riemann_zeta_deriv_zero_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:06:59.349685+00:00
-- url     : https://prove2.me/submissions/9675d8ed-36db-402e-af57-d565c4f0314f

import Mathlib

theorem solution : deriv riemannZeta 0 = -Complex.log (2 * (Real.pi : ℂ)) / 2 :=
  deriv_riemannZeta_zero
