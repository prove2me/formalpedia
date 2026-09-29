-- Prove2me | solution 1 for FiniteTriangular.sum_range_365
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:41:23.86588+00:00
-- url     : https://prove2.me/submissions/e1ca34fc-0463-4078-bc7d-4be163e9bc61

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 365, k = 66430 := by
  rw [sum_range_id]
