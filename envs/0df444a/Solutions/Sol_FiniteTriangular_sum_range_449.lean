-- Prove2me | solution 1 for FiniteTriangular.sum_range_449
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:09:59.500583+00:00
-- url     : https://prove2.me/submissions/d3ac50cf-db88-40e6-bea5-444586f22ec9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 449, k = 100576 := by
  rw [sum_range_id]
