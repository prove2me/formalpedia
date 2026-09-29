-- Prove2me | solution 1 for FiniteTriangular.sum_range_683
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:02:00.949491+00:00
-- url     : https://prove2.me/submissions/4f77427e-79db-4a18-b300-8af3239c3925

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 683, k = 232903 := by
  rw [sum_range_id]
