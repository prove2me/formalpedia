-- Prove2me | solution 1 for FiniteTriangular.sum_range_392
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:47:10.652962+00:00
-- url     : https://prove2.me/submissions/c0654025-23cd-493b-b5d2-b641e12f9fdf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 392, k = 76636 := by
  rw [sum_range_id]
