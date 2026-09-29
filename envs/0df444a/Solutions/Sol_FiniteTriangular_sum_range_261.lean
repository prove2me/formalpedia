-- Prove2me | solution 1 for FiniteTriangular.sum_range_261
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:11:15.456554+00:00
-- url     : https://prove2.me/submissions/ce769cda-b33d-49be-99aa-a0ce3e0203d3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 261, k = 33930 := by
  rw [sum_range_id]
