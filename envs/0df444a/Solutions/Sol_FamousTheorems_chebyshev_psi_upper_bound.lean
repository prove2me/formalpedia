-- Prove2me | solution 1 for FamousTheorems.chebyshev_psi_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:16:36.559206+00:00
-- url     : https://prove2.me/submissions/67181ac5-3012-4f4c-b59b-a71983ded402

import Mathlib

theorem solution {x : ℝ} (hx : 0 ≤ x) :
    Chebyshev.psi x ≤ (Real.log 4 + 4) * x :=
  Chebyshev.psi_le_const_mul_self hx
