-- Prove2me | solution 1 for FiniteTriangular.sum_range_629
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:50:05.516328+00:00
-- url     : https://prove2.me/submissions/a5025388-b08c-4ed4-a743-de0cccb82213

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 629, k = 197506 := by
  rw [sum_range_id]
