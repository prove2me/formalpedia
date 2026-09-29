-- Prove2me | solution 1 for FiniteTriangular.sum_range_362
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:41:22.075976+00:00
-- url     : https://prove2.me/submissions/0c309ed6-41ec-4400-8552-bf403a9b92f2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 362, k = 65341 := by
  rw [sum_range_id]
