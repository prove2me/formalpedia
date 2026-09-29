-- Prove2me | solution 1 for FiniteTriangular.sum_range_193
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:47:31.624429+00:00
-- url     : https://prove2.me/submissions/4265e26d-6a6a-4b34-8d19-a3cb637414b6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 193, k = 18528 := by
  rw [sum_range_id]
