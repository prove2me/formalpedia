-- Prove2me | solution 1 for FiniteTriangular.sum_range_924
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:53:46.75202+00:00
-- url     : https://prove2.me/submissions/3ed4de2f-8f2c-4161-8866-b308dbbde687

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 924, k = 426426 := by
  rw [sum_range_id]
