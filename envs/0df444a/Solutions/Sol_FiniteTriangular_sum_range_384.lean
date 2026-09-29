-- Prove2me | solution 1 for FiniteTriangular.sum_range_384
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:45:24.778091+00:00
-- url     : https://prove2.me/submissions/dbf59df4-0c96-47a8-b7d5-5b1bb35d9363

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 384, k = 73536 := by
  rw [sum_range_id]
