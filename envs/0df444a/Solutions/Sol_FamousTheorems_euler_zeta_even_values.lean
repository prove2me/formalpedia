-- Prove2me | solution 1 for FamousTheorems.euler_zeta_even_values
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:06:18.511835+00:00
-- url     : https://prove2.me/submissions/6e425e1f-6612-4bc0-92dd-540a4fba65a7

import Mathlib

theorem solution {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => 1 / (n : ℝ) ^ (2 * k))
      ((-1) ^ (k + 1) * 2 ^ (2 * k - 1) * Real.pi ^ (2 * k) * (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ)) :=
  hasSum_zeta_nat hk
