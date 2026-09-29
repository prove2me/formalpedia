-- Prove2me | solution 1 for FamousTheorems.riemann_zeta_euler_product
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:04:01.035655+00:00
-- url     : https://prove2.me/submissions/eba416d1-5778-4352-a544-c288ad4e79d2

import Mathlib

theorem solution {s : ℂ} (hs : 1 < s.re) : ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℂ) ^ (-s))⁻¹ = riemannZeta s :=
  riemannZeta_eulerProduct_tprod hs
