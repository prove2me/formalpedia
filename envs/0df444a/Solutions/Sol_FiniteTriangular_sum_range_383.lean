-- Prove2me | solution 1 for FiniteTriangular.sum_range_383
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:45:24.227319+00:00
-- url     : https://prove2.me/submissions/712a7021-5281-4c1c-8599-d98cda787bc3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 383, k = 73153 := by
  rw [sum_range_id]
