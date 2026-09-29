-- Prove2me | solution 1 for FiniteTriangular.sum_range_737
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:14:42.041231+00:00
-- url     : https://prove2.me/submissions/df9ca6a5-e027-4ec1-96d5-1574440e6327

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 737, k = 271216 := by
  rw [sum_range_id]
