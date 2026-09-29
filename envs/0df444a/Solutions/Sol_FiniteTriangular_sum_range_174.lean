-- Prove2me | solution 1 for FiniteTriangular.sum_range_174
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:22:17.824801+00:00
-- url     : https://prove2.me/submissions/7effcf8a-6624-4f45-9925-0229527b70d4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 174, k = 15051 := by
  rw [sum_range_id]
