-- Prove2me | solution 1 for FiniteTriangular.sum_range_416
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:52:20.382459+00:00
-- url     : https://prove2.me/submissions/16265120-74e8-45d2-bb65-7cc33e1e7823

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 416, k = 86320 := by
  rw [sum_range_id]
