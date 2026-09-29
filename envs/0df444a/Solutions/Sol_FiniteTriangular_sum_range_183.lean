-- Prove2me | solution 1 for FiniteTriangular.sum_range_183
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:24:29.558593+00:00
-- url     : https://prove2.me/submissions/86794d30-f203-488f-a223-c8c52da9b6ab

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 183, k = 16653 := by
  rw [sum_range_id]
