-- Prove2me | solution 1 for FiniteTriangular.sum_range_658
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:56:47.46268+00:00
-- url     : https://prove2.me/submissions/c11f73a3-31e5-4984-9a80-36f92a243f24

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 658, k = 216153 := by
  rw [sum_range_id]
