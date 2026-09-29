-- Prove2me | solution 1 for FiniteTriangular.sum_range_761
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:19:48.120115+00:00
-- url     : https://prove2.me/submissions/61e62311-46e4-4403-b00b-9ef9d36490f8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 761, k = 289180 := by
  rw [sum_range_id]
