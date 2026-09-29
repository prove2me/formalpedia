-- Prove2me | solution 1 for FiniteTriangular.sum_range_567
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:36:20.84089+00:00
-- url     : https://prove2.me/submissions/703de6ef-8aee-4b25-9ae9-84c7c1b1f612

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 567, k = 160461 := by
  rw [sum_range_id]
