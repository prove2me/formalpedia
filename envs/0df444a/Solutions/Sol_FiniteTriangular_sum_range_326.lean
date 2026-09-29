-- Prove2me | solution 1 for FiniteTriangular.sum_range_326
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:32:33.196925+00:00
-- url     : https://prove2.me/submissions/9d58549a-d9fd-4c0e-8efe-47e596a5801a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 326, k = 52975 := by
  rw [sum_range_id]
