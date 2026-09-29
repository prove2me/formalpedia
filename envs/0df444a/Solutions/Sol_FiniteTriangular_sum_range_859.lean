-- Prove2me | solution 1 for FiniteTriangular.sum_range_859
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:40:10.719042+00:00
-- url     : https://prove2.me/submissions/9505bdad-4816-4d06-b3d2-b0559229aa61

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 859, k = 368511 := by
  rw [sum_range_id]
