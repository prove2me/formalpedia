-- Prove2me | solution 1 for FiniteTriangular.sum_range_931
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:55:33.249921+00:00
-- url     : https://prove2.me/submissions/9a98535b-414f-44e2-8a5b-c781c228597a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 931, k = 432915 := by
  rw [sum_range_id]
