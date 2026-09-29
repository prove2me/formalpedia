-- Prove2me | solution 1 for FiniteTriangular.sum_range_769
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:21:36.782033+00:00
-- url     : https://prove2.me/submissions/599bb9e9-172a-4647-b896-134f96a212b1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 769, k = 295296 := by
  rw [sum_range_id]
