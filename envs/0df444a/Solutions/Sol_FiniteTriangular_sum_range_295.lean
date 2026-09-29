-- Prove2me | solution 1 for FiniteTriangular.sum_range_295
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:18:21.013153+00:00
-- url     : https://prove2.me/submissions/a356d198-7bbe-4a7d-b11a-53ff1c0c78f5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 295, k = 43365 := by
  rw [sum_range_id]
