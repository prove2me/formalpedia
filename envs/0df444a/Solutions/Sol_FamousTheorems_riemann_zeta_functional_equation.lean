-- Prove2me | solution 1 for FamousTheorems.riemann_zeta_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:03:40.678727+00:00
-- url     : https://prove2.me/submissions/bf5fe595-ec8f-40a7-8b5d-a85f3ec39eba

import Mathlib

theorem solution {s : ℂ} (hs : ∀ n : ℕ, s ≠ -(n : ℂ)) (hs' : s ≠ 1) :
    riemannZeta (1 - s) =
      2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2) * riemannZeta s :=
  riemannZeta_one_sub hs hs'
