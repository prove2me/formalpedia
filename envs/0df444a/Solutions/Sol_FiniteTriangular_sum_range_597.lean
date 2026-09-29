-- Prove2me | solution 1 for FiniteTriangular.sum_range_597
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:43:10.639142+00:00
-- url     : https://prove2.me/submissions/9407a028-e9e4-4a29-baa2-e853b7fc3a1b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 597, k = 177906 := by
  rw [sum_range_id]
