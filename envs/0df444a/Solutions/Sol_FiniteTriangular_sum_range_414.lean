-- Prove2me | solution 1 for FiniteTriangular.sum_range_414
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:52:19.258001+00:00
-- url     : https://prove2.me/submissions/dcb35ccc-bd10-4a3a-9372-ea2745b1d36b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 414, k = 85491 := by
  rw [sum_range_id]
