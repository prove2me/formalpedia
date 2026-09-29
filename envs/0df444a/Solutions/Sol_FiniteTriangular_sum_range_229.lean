-- Prove2me | solution 1 for FiniteTriangular.sum_range_229
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:55:13.663675+00:00
-- url     : https://prove2.me/submissions/63d99164-59f5-44dd-816c-d81b318c0c80

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 229, k = 26106 := by
  rw [sum_range_id]
