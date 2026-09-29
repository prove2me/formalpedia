-- Prove2me | solution 1 for FiniteTriangular.sum_range_942
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:57:13.044577+00:00
-- url     : https://prove2.me/submissions/31440f89-2cfc-4e8f-a5cf-de76fa0569a5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 942, k = 443211 := by
  rw [sum_range_id]
