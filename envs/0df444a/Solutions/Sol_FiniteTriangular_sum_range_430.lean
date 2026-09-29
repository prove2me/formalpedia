-- Prove2me | solution 1 for FiniteTriangular.sum_range_430
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:55:52.653917+00:00
-- url     : https://prove2.me/submissions/397e4c97-1943-496d-a113-d82c1e75833e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 430, k = 92235 := by
  rw [sum_range_id]
