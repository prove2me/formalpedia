-- Prove2me | solution 1 for FiniteTriangular.sum_range_915
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:51:59.109578+00:00
-- url     : https://prove2.me/submissions/c5052f8c-b754-4784-ad0f-f5b17a04afe9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 915, k = 418155 := by
  rw [sum_range_id]
