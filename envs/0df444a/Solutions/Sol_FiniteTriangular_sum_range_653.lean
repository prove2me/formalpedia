-- Prove2me | solution 1 for FiniteTriangular.sum_range_653
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:55:03.962369+00:00
-- url     : https://prove2.me/submissions/6cf15ab3-396d-45e0-9591-f99c39ca8e69

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 653, k = 212878 := by
  rw [sum_range_id]
