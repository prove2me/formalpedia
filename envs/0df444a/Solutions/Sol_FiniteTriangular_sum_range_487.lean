-- Prove2me | solution 1 for FiniteTriangular.sum_range_487
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:17:24.281119+00:00
-- url     : https://prove2.me/submissions/50bee04a-95e7-46b5-8ba3-720b4d04b8ef

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 487, k = 118341 := by
  rw [sum_range_id]
