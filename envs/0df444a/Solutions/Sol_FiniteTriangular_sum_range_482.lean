-- Prove2me | solution 1 for FiniteTriangular.sum_range_482
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:17:21.223823+00:00
-- url     : https://prove2.me/submissions/743bebef-05ae-4de5-a88c-6f23a31d8116

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 482, k = 115921 := by
  rw [sum_range_id]
