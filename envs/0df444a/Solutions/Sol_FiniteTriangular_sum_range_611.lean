-- Prove2me | solution 1 for FiniteTriangular.sum_range_611
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:46:42.757458+00:00
-- url     : https://prove2.me/submissions/f2f928a4-bb48-4263-a98c-7dafeb6517c0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 611, k = 186355 := by
  rw [sum_range_id]
