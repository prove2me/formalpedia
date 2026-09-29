-- Prove2me | solution 1 for FiniteTriangular.sum_range_687
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:02:04.653022+00:00
-- url     : https://prove2.me/submissions/55f0b7b4-4127-4c21-8a9f-1862666a1c5a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 687, k = 235641 := by
  rw [sum_range_id]
