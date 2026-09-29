-- Prove2me | solution 1 for FiniteTriangular.sum_range_1088
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:22:31.15288+00:00
-- url     : https://prove2.me/submissions/f8292694-4f32-474c-a227-d196574b0105

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1088, k = 591328 := by
  rw [sum_range_id]
