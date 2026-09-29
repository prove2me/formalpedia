-- Prove2me | solution 1 for FiniteTriangular.sum_range_848
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:36:59.674134+00:00
-- url     : https://prove2.me/submissions/b2ed5257-2881-4f15-b72d-f1c9f5471aa8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 848, k = 359128 := by
  rw [sum_range_id]
