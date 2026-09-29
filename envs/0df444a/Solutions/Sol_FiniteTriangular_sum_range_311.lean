-- Prove2me | solution 1 for FiniteTriangular.sum_range_311
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:22:08.3534+00:00
-- url     : https://prove2.me/submissions/541b897e-882d-4cf7-8862-7f907cf674f9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 311, k = 48205 := by
  rw [sum_range_id]
