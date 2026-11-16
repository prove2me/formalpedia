-- Prove2me | solution 1 for ExternalTowerTest.averaging_minus
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:32:19.015505+00:00
-- url     : https://prove2.me/submissions/ec0faf62-ad6f-44fc-9c01-2e43313ea3a1

import Mathlib
open Filter Topology

theorem solution (k : ℕ) :
    ((1 - (2 : ℝ)^k)/2) = (1/4 : ℝ)*((1 + (2 : ℝ)^(k+1))/2) + (3/4 : ℝ)*((1 - (2 : ℝ)^(k+1))/2) := by
  rw [pow_succ]
  ring
