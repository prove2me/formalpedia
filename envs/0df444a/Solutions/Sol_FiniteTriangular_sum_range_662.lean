-- Prove2me | solution 1 for FiniteTriangular.sum_range_662
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:56:49.850768+00:00
-- url     : https://prove2.me/submissions/abdc358a-a860-48d5-8be3-51ca4dcefc3b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 662, k = 218791 := by
  rw [sum_range_id]
