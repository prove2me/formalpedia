-- Prove2me | solution 1 for FiniteTriangular.sum_range_536
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:27:32.633683+00:00
-- url     : https://prove2.me/submissions/cb9bc477-3d3b-40a7-a742-da87294ddc08

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 536, k = 143380 := by
  rw [sum_range_id]
