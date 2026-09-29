-- Prove2me | solution 1 for FiniteTriangular.sum_range_575
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:38:06.500579+00:00
-- url     : https://prove2.me/submissions/653f5cb1-775a-4d00-9b28-fa8c822af4ca

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 575, k = 165025 := by
  rw [sum_range_id]
