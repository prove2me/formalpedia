-- Prove2me | solution 1 for FiniteTriangular.sum_range_685
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:02:03.410912+00:00
-- url     : https://prove2.me/submissions/2862bf3f-1273-4229-96b1-467eb2165ea2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 685, k = 234270 := by
  rw [sum_range_id]
