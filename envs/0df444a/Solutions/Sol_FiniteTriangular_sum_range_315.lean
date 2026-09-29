-- Prove2me | solution 1 for FiniteTriangular.sum_range_315
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:30:35.677761+00:00
-- url     : https://prove2.me/submissions/33a84ce2-40b8-4063-b280-10cee11a5b35

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 315, k = 49455 := by
  rw [sum_range_id]
