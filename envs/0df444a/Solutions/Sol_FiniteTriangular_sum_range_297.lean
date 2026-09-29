-- Prove2me | solution 1 for FiniteTriangular.sum_range_297
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:20:04.127158+00:00
-- url     : https://prove2.me/submissions/27c71cb7-ddf6-4f32-9e20-7b62669e7d5c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 297, k = 43956 := by
  rw [sum_range_id]
