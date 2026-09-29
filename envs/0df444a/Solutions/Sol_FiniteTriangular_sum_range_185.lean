-- Prove2me | solution 1 for FiniteTriangular.sum_range_185
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:45:15.693267+00:00
-- url     : https://prove2.me/submissions/298500a7-1845-4f57-9d8f-2c837e227a21

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 185, k = 17020 := by
  rw [sum_range_id]
