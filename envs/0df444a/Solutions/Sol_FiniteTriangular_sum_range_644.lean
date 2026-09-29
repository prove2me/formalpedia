-- Prove2me | solution 1 for FiniteTriangular.sum_range_644
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:53:25.753003+00:00
-- url     : https://prove2.me/submissions/6f16bcde-e367-4604-b6e4-fd4717d49d74

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 644, k = 207046 := by
  rw [sum_range_id]
