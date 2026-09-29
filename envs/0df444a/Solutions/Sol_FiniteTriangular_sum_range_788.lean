-- Prove2me | solution 1 for FiniteTriangular.sum_range_788
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:25:07.474573+00:00
-- url     : https://prove2.me/submissions/1ac750b3-f229-4a74-9e3c-5781b5092a7d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 788, k = 310078 := by
  rw [sum_range_id]
