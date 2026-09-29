-- Prove2me | solution 1 for FiniteTriangular.sum_range_161
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:19:15.118891+00:00
-- url     : https://prove2.me/submissions/3ca77100-4ca8-4e2f-b086-50923ca9315a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 161, k = 12880 := by
  rw [sum_range_id]
