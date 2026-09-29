-- Prove2me | solution 1 for FiniteTriangular.sum_range_599
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:43:11.773659+00:00
-- url     : https://prove2.me/submissions/5f17038d-e941-4e08-aa51-ba06572282d6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 599, k = 179101 := by
  rw [sum_range_id]
