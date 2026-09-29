-- Prove2me | solution 1 for FiniteTriangular.sum_range_371
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:43:16.391783+00:00
-- url     : https://prove2.me/submissions/24860427-c58f-4e1a-b1df-f29df84ca167

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 371, k = 68635 := by
  rw [sum_range_id]
