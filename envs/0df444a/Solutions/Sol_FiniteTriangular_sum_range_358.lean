-- Prove2me | solution 1 for FiniteTriangular.sum_range_358
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:39:29.549056+00:00
-- url     : https://prove2.me/submissions/95c7cde1-6510-4b19-96d8-8e2d1028c5dd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 358, k = 63903 := by
  rw [sum_range_id]
