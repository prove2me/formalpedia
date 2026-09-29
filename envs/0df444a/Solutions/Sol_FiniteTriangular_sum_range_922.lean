-- Prove2me | solution 1 for FiniteTriangular.sum_range_922
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:53:45.351791+00:00
-- url     : https://prove2.me/submissions/5a79ce80-a3a5-4951-9bed-4f2144a3f416

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 922, k = 424581 := by
  rw [sum_range_id]
