-- Prove2me | solution 1 for FiniteTriangular.sum_range_635
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:51:50.556985+00:00
-- url     : https://prove2.me/submissions/56034c95-fd0d-4c03-937a-36ef72c74ee8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 635, k = 201295 := by
  rw [sum_range_id]
