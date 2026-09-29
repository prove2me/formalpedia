-- Prove2me | solution 1 for FiniteTriangular.sum_range_456
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:10:04.737607+00:00
-- url     : https://prove2.me/submissions/8099b24a-6bd5-464a-aae3-115aac39133e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 456, k = 103740 := by
  rw [sum_range_id]
