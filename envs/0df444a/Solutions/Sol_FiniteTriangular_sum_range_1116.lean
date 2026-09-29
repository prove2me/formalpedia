-- Prove2me | solution 1 for FiniteTriangular.sum_range_1116
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:29:07.414136+00:00
-- url     : https://prove2.me/submissions/c8e9cc7d-32e9-42ad-a5b1-96cc8d1356d7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1116, k = 622170 := by
  rw [sum_range_id]
