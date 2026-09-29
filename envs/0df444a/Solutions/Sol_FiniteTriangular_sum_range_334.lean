-- Prove2me | solution 1 for FiniteTriangular.sum_range_334
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:34:20.053224+00:00
-- url     : https://prove2.me/submissions/c872e4d8-dec1-4a38-aab3-3c673307f28d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 334, k = 55611 := by
  rw [sum_range_id]
