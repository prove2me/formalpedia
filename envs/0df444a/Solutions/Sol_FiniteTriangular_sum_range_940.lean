-- Prove2me | solution 1 for FiniteTriangular.sum_range_940
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:57:11.540203+00:00
-- url     : https://prove2.me/submissions/574ee94e-3f71-4056-8066-f3671b887a62

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 940, k = 441330 := by
  rw [sum_range_id]
