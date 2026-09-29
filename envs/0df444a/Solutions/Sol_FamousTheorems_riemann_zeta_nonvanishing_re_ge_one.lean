-- Prove2me | solution 1 for FamousTheorems.riemann_zeta_nonvanishing_re_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:04:29.192754+00:00
-- url     : https://prove2.me/submissions/08db2586-0498-4a1a-beab-30fe09a59e3c

import Mathlib

theorem solution {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs
