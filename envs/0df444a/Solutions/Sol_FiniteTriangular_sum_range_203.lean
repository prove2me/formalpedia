-- Prove2me | solution 1 for FiniteTriangular.sum_range_203
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:49:27.897235+00:00
-- url     : https://prove2.me/submissions/30053e82-b62c-4005-a014-4e6101bc3d4b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 203, k = 20503 := by
  rw [sum_range_id]
