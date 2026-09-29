-- Prove2me | solution 1 for FiniteTriangular.sum_range_858
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:40:10.062252+00:00
-- url     : https://prove2.me/submissions/9f128213-2bed-4610-96d4-1c5fc5846e05

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 858, k = 367653 := by
  rw [sum_range_id]
