-- Prove2me | solution 1 for FiniteTriangular.sum_range_382
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:45:23.669914+00:00
-- url     : https://prove2.me/submissions/f691e690-58e4-4419-8d7d-c8321b8b45b6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 382, k = 72771 := by
  rw [sum_range_id]
