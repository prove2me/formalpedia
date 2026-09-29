-- Prove2me | solution 1 for FiniteTriangular.sum_range_457
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:12:01.812381+00:00
-- url     : https://prove2.me/submissions/af18e935-c8d8-4931-b8ee-80a482c54907

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 457, k = 104196 := by
  rw [sum_range_id]
