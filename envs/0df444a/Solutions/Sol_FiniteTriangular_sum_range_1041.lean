-- Prove2me | solution 1 for FiniteTriangular.sum_range_1041
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:13:16.69661+00:00
-- url     : https://prove2.me/submissions/325b761c-1e5d-44fb-a74b-94b8cd6450b1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1041, k = 541320 := by
  rw [sum_range_id]
