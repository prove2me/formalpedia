-- Prove2me | solution 1 for FiniteTriangular.sum_range_752
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:16:34.77559+00:00
-- url     : https://prove2.me/submissions/aa4f2a9e-fbb8-45e7-890d-86a020ddd765

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 752, k = 282376 := by
  rw [sum_range_id]
