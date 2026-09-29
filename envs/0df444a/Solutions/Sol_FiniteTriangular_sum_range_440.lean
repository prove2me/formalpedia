-- Prove2me | solution 1 for FiniteTriangular.sum_range_440
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:57:38.503389+00:00
-- url     : https://prove2.me/submissions/08ab283e-bd5c-4ab5-b593-d77d2ca68cc4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 440, k = 96580 := by
  rw [sum_range_id]
