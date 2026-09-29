-- Prove2me | solution 1 for FiniteTriangular.sum_range_1036
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:47:56.715983+00:00
-- url     : https://prove2.me/submissions/e1c610cf-150d-4d76-a7bb-8b1e7903dd35

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1036, k = 536130 := by
  rw [sum_range_id]
