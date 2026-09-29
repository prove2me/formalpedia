-- Prove2me | solution 1 for FiniteTriangular.sum_range_568
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:36:21.436246+00:00
-- url     : https://prove2.me/submissions/283a8d0d-26b2-4c9b-9d99-7b96c915ca19

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 568, k = 161028 := by
  rw [sum_range_id]
