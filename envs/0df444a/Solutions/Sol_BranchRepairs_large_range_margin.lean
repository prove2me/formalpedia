-- Prove2me | solution 1 for BranchRepairs.large_range_margin
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:29:45.203661+00:00
-- url     : https://prove2.me/submissions/75c1b0da-bd72-4631-b1e9-242614f089e3

import Mathlib
open Filter Topology

theorem solution :
    (1010000:ℝ)*24/(98:ℝ)^4 < 1/2 := by norm_num

-- Algebraic result only. The analytic tail estimates are explicit hypotheses.
