-- Prove2me | solution 1 for FiniteTriangular.sum_range_773
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:21:39.186472+00:00
-- url     : https://prove2.me/submissions/0dfed227-8c8e-479a-a2d8-a861d4b35f39

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 773, k = 298378 := by
  rw [sum_range_id]
