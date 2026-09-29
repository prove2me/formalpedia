-- Prove2me | solution 1 for FiniteTriangular.sum_range_370
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:43:15.871574+00:00
-- url     : https://prove2.me/submissions/aa04c9b3-89a7-4faa-a567-caae6eb31c86

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 370, k = 68265 := by
  rw [sum_range_id]
