-- Prove2me | solution 1 for FamousTheorems.chebyshev_theta_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T08:18:03.707983+00:00
-- url     : https://prove2.me/submissions/2f10a0e5-3552-45e4-9d07-2886c21ae331

import Mathlib

theorem solution (n : ℕ) :
    (n : ℝ) * Real.log 2 - Real.log (n + 1) - 2 * Real.sqrt n * Real.log n ≤ Chebyshev.theta n :=
  Chebyshev.theta_ge n
