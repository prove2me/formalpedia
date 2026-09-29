-- Prove2me | solution 1 for FiniteTriangular.sum_range_488
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:17:24.852894+00:00
-- url     : https://prove2.me/submissions/511590bb-45a1-4400-bc07-6964a5f4c309

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 488, k = 118828 := by
  rw [sum_range_id]
