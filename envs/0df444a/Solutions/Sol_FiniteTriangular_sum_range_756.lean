-- Prove2me | solution 1 for FiniteTriangular.sum_range_756
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:18:12.935705+00:00
-- url     : https://prove2.me/submissions/12b265fa-0698-4c8b-8eef-d218ab917c11

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 756, k = 285390 := by
  rw [sum_range_id]
