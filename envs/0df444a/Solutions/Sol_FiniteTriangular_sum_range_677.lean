-- Prove2me | solution 1 for FiniteTriangular.sum_range_677
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:00:13.626425+00:00
-- url     : https://prove2.me/submissions/61494021-591e-4796-87e5-9fd7e637b217

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 677, k = 228826 := by
  rw [sum_range_id]
