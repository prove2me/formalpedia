-- Prove2me | solution 1 for FiniteTriangular.sum_range_506
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:22:20.174428+00:00
-- url     : https://prove2.me/submissions/fc1605e6-0629-4e49-8541-c6543b95891f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 506, k = 127765 := by
  rw [sum_range_id]
