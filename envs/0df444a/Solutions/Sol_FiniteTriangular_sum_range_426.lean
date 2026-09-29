-- Prove2me | solution 1 for FiniteTriangular.sum_range_426
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:55:49.587827+00:00
-- url     : https://prove2.me/submissions/a7465fdc-2277-4763-9599-c8ab4a2b3dcc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 426, k = 90525 := by
  rw [sum_range_id]
