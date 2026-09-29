-- Prove2me | solution 1 for FiniteTriangular.sum_range_839
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:35:23.283302+00:00
-- url     : https://prove2.me/submissions/e6d0f0e7-7e7a-4aa1-941c-02a9a01c7bfb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 839, k = 351541 := by
  rw [sum_range_id]
