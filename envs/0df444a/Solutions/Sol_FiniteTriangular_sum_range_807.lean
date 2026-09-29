-- Prove2me | solution 1 for FiniteTriangular.sum_range_807
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:28:30.718472+00:00
-- url     : https://prove2.me/submissions/91d4ad2b-618c-44ef-9d07-f862c7d9e168

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 807, k = 325221 := by
  rw [sum_range_id]
