-- Prove2me | solution 1 for FiniteTriangular.sum_range_310
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:22:07.692443+00:00
-- url     : https://prove2.me/submissions/efd8ad9d-7d5c-4a01-8c94-d930f6ede381

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 310, k = 47895 := by
  rw [sum_range_id]
