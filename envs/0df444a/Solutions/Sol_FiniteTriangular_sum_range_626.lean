-- Prove2me | solution 1 for FiniteTriangular.sum_range_626
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:50:03.415885+00:00
-- url     : https://prove2.me/submissions/7a7d2182-7501-4f09-a90e-2852e7ee27ef

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 626, k = 195625 := by
  rw [sum_range_id]
