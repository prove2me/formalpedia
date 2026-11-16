-- Prove2me | solution 1 for BranchRepairs.small_range_margin
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:29:38.575092+00:00
-- url     : https://prove2.me/submissions/846a6d6b-0687-4737-a38b-594be71b01cf

import Mathlib
open Filter Topology

theorem solution :
    (9*24 : ℝ) * (1/(10000:ℝ)^2 + 1/(10000:ℝ)^3) < 1/2 := by norm_num
