-- Prove2me | solution 1 for ExternalTowerTest.base_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-16T03:32:26.14131+00:00
-- url     : https://prove2.me/submissions/2714dc87-f3ab-4363-92dc-47cbf20de165

import Mathlib
open Filter Topology

theorem solution : 0 ≤ ((1 + (2 : ℝ)^0)/2) ∧ 0 ≤ ((1 - (2 : ℝ)^0)/2) := by
  norm_num
