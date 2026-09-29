-- Prove2me | solution 1 for FiniteTriangular.sum_range_1013
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:42:29.460984+00:00
-- url     : https://prove2.me/submissions/4676741f-cf2c-405c-bfe1-91188e131d61

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1013, k = 512578 := by
  rw [sum_range_id]
