-- Prove2me | solution 1 for FiniteTriangular.sum_range_70
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:33:05.944562+00:00
-- url     : https://prove2.me/submissions/9247c072-14cd-4ee2-8b1a-46786b423b57

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 70, k = 2415 := by
  decide
