-- Prove2me | solution 1 for FiniteTriangular.sum_range_168
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:20:41.310957+00:00
-- url     : https://prove2.me/submissions/f3cf0749-6411-4b8a-bdfe-df89b94ce3f2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 168, k = 14028 := by
  rw [sum_range_id]
