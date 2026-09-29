-- Prove2me | solution 1 for FiniteTriangular.sum_range_455
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:10:04.072006+00:00
-- url     : https://prove2.me/submissions/3ec9802c-28fc-4975-86b4-bc23acc3209b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 455, k = 103285 := by
  rw [sum_range_id]
