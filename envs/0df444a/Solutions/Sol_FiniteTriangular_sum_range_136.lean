-- Prove2me | solution 1 for FiniteTriangular.sum_range_136
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:14:48.387297+00:00
-- url     : https://prove2.me/submissions/c910dab1-fc3d-4985-9246-a0bbad8b20e5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 136, k = 9180 := by
  rw [sum_range_id]
