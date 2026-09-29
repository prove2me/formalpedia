-- Prove2me | solution 1 for FiniteTriangular.sum_range_913
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:51:57.851951+00:00
-- url     : https://prove2.me/submissions/dd7c6fba-3bad-4867-b0ec-1153b4976f2b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 913, k = 416328 := by
  rw [sum_range_id]
