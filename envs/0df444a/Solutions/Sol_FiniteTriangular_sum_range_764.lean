-- Prove2me | solution 1 for FiniteTriangular.sum_range_764
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:19:50.551286+00:00
-- url     : https://prove2.me/submissions/700274fb-8916-4454-a934-8d3bafef97e6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 764, k = 291466 := by
  rw [sum_range_id]
