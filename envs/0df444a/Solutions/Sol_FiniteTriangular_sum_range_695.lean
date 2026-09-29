-- Prove2me | solution 1 for FiniteTriangular.sum_range_695
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:03:40.369104+00:00
-- url     : https://prove2.me/submissions/fe64ea03-1ace-4433-949c-08adece094ae

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 695, k = 241165 := by
  rw [sum_range_id]
