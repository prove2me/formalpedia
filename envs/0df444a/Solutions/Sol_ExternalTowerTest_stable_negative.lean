-- Prove2me | solution 1 for ExternalTowerTest.stable_negative
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:33:50.241075+00:00
-- url     : https://prove2.me/submissions/4bea5b59-8121-44be-816c-e9d857763854

import Mathlib
open Filter Topology

theorem solution (v w e d : ℝ)
    (hv : v ≤ -d) (herr : |w-v| ≤ e) (he : e < d) : w < 0 := by
  have hu := (abs_le.mp herr).2
  linarith
