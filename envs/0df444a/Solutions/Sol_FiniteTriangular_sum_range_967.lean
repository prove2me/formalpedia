-- Prove2me | solution 1 for FiniteTriangular.sum_range_967
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:02:49.747612+00:00
-- url     : https://prove2.me/submissions/401efcbd-d619-4faf-b414-51be9064dd01

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 967, k = 467061 := by
  rw [sum_range_id]
