-- Prove2me | solution 1 for ExternalTowerTest.mass_one
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:31:13.291732+00:00
-- url     : https://prove2.me/submissions/096720ea-c2ee-4c8b-a94c-01fb19328a1b

import Mathlib
open Filter Topology

theorem solution (k : ℕ) : ((1 + (2 : ℝ)^k)/2) + ((1 - (2 : ℝ)^k)/2) = 1 := by
  ring
