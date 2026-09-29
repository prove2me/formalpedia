-- Prove2me | solution 1 for FiniteTriangular.sum_range_524
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:25:52.751172+00:00
-- url     : https://prove2.me/submissions/51de2080-1bd6-4b9c-a525-662569351c8c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 524, k = 137026 := by
  rw [sum_range_id]
