-- Prove2me | solution 1 for FiniteTriangular.sum_range_302
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:20:07.55791+00:00
-- url     : https://prove2.me/submissions/2707c4d6-430c-495a-b7c4-4ab94e8509d8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 302, k = 45451 := by
  rw [sum_range_id]
