-- Prove2me | solution 1 for ExternalTowerTest.averaging_plus
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:31:21.495243+00:00
-- url     : https://prove2.me/submissions/762c86bc-9617-461b-bfe4-df7b8933956e

import Mathlib
open Filter Topology

theorem solution (k : ℕ) :
    ((1 + (2 : ℝ)^k)/2) = (3/4 : ℝ)*((1 + (2 : ℝ)^(k+1))/2) + (1/4 : ℝ)*((1 - (2 : ℝ)^(k+1))/2) := by
  rw [pow_succ]
  ring
