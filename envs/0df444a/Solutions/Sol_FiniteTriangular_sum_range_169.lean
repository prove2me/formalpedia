-- Prove2me | solution 1 for FiniteTriangular.sum_range_169
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:20:42.118383+00:00
-- url     : https://prove2.me/submissions/9d13c509-b638-4ee7-aabd-f67865ce2f7a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 169, k = 14196 := by
  rw [sum_range_id]
