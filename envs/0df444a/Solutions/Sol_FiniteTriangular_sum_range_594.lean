-- Prove2me | solution 1 for FiniteTriangular.sum_range_594
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:43:08.977339+00:00
-- url     : https://prove2.me/submissions/69388ffc-5055-476f-9e36-d4ed5bf08090

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 594, k = 176121 := by
  rw [sum_range_id]
