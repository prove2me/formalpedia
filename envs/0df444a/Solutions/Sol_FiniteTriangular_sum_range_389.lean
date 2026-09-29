-- Prove2me | solution 1 for FiniteTriangular.sum_range_389
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:47:08.698895+00:00
-- url     : https://prove2.me/submissions/a55f76bb-c188-4b2e-916a-d252654fcc55

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 389, k = 75466 := by
  rw [sum_range_id]
