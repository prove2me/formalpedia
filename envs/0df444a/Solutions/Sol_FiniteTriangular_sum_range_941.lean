-- Prove2me | solution 1 for FiniteTriangular.sum_range_941
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:57:12.348412+00:00
-- url     : https://prove2.me/submissions/560db6b0-fa43-4a51-8ef3-8d859ad0c4e3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 941, k = 442270 := by
  rw [sum_range_id]
