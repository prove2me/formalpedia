-- Prove2me | solution 1 for FiniteTriangular.sum_range_1029
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:45:56.842659+00:00
-- url     : https://prove2.me/submissions/ed9ae9e4-e251-401a-82d8-d8d13701d0aa

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1029, k = 528906 := by
  rw [sum_range_id]
