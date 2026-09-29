-- Prove2me | solution 1 for FiniteTriangular.sum_range_696
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:03:40.882831+00:00
-- url     : https://prove2.me/submissions/13ec53d1-8956-4142-8a97-75d006ffcae8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 696, k = 241860 := by
  rw [sum_range_id]
