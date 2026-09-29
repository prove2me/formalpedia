-- Prove2me | solution 1 for FiniteTriangular.sum_range_218
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:53:26.09161+00:00
-- url     : https://prove2.me/submissions/06617616-cdd8-4718-add3-ea1332909c54

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 218, k = 23653 := by
  rw [sum_range_id]
