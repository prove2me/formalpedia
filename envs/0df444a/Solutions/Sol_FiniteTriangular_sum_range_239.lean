-- Prove2me | solution 1 for FiniteTriangular.sum_range_239
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:57:47.118985+00:00
-- url     : https://prove2.me/submissions/71ac854b-687c-4858-a49c-0e859cbec773

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 239, k = 28441 := by
  rw [sum_range_id]
