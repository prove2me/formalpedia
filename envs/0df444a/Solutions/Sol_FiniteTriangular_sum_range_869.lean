-- Prove2me | solution 1 for FiniteTriangular.sum_range_869
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:41:59.498881+00:00
-- url     : https://prove2.me/submissions/8ab19ff4-bd92-49a7-bf5b-fab02519b1d3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 869, k = 377146 := by
  rw [sum_range_id]
