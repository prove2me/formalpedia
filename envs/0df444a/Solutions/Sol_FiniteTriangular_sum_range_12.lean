-- Prove2me | solution 1 for FiniteTriangular.sum_range_12
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:04:07.528984+00:00
-- url     : https://prove2.me/submissions/e139ffc1-a022-4d71-a711-ea0ee12fa736

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 12, k = 66 := by
  decide
