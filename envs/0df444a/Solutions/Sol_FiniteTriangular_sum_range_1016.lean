-- Prove2me | solution 1 for FiniteTriangular.sum_range_1016
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:42:31.365985+00:00
-- url     : https://prove2.me/submissions/a9501598-35ad-4ec1-8fc2-a588aef9f7bc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1016, k = 515620 := by
  rw [sum_range_id]
