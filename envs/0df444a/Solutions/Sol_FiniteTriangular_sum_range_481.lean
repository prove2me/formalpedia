-- Prove2me | solution 1 for FiniteTriangular.sum_range_481
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:17:20.452519+00:00
-- url     : https://prove2.me/submissions/ba933a52-176d-4fa6-8760-d1f593b9dc13

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 481, k = 115440 := by
  rw [sum_range_id]
