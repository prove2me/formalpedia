-- Prove2me | solution 1 for FiniteTriangular.sum_range_522
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:25:51.490114+00:00
-- url     : https://prove2.me/submissions/835ca927-7008-4847-b627-b92be8686587

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 522, k = 135981 := by
  rw [sum_range_id]
