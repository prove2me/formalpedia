-- Prove2me | solution 1 for FiniteTriangular.sum_range_645
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:53:26.318633+00:00
-- url     : https://prove2.me/submissions/bf01aaaf-6871-475a-858b-9f1c05e8f4a0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 645, k = 207690 := by
  rw [sum_range_id]
