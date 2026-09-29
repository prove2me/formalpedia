-- Prove2me | solution 1 for FiniteTriangular.sum_range_783
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:23:25.515825+00:00
-- url     : https://prove2.me/submissions/886dbb15-e815-4f1f-83db-b6e835da95e4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 783, k = 306153 := by
  rw [sum_range_id]
