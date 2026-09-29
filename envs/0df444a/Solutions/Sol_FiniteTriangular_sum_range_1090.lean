-- Prove2me | solution 1 for FiniteTriangular.sum_range_1090
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:23:58.945457+00:00
-- url     : https://prove2.me/submissions/e0ec79c5-be57-40a1-81e8-d49395d010c4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1090, k = 593505 := by
  rw [sum_range_id]
