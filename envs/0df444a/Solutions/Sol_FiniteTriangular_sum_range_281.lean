-- Prove2me | solution 1 for FiniteTriangular.sum_range_281
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:16:40.562264+00:00
-- url     : https://prove2.me/submissions/b3fe9080-f0c7-4729-9e10-2d553a7fffc8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 281, k = 39340 := by
  rw [sum_range_id]
