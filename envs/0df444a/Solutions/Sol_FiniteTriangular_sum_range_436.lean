-- Prove2me | solution 1 for FiniteTriangular.sum_range_436
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:57:36.112512+00:00
-- url     : https://prove2.me/submissions/b7dea3b2-cc99-474d-8427-443fc258cbbe

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 436, k = 94830 := by
  rw [sum_range_id]
