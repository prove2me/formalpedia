-- Prove2me | solution 1 for FiniteTriangular.sum_range_439
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:57:37.931976+00:00
-- url     : https://prove2.me/submissions/f19142bc-f4cc-4501-9e18-7b12919d0e15

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 439, k = 96141 := by
  rw [sum_range_id]
