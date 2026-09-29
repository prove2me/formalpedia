-- Prove2me | solution 1 for FiniteTriangular.sum_range_751
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:16:34.179138+00:00
-- url     : https://prove2.me/submissions/44c5a36b-4445-474a-b797-cf122c545f29

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 751, k = 281625 := by
  rw [sum_range_id]
