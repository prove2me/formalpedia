-- Prove2me | solution 1 for FiniteTriangular.sum_range_573
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:38:05.283253+00:00
-- url     : https://prove2.me/submissions/e4124b6a-06ef-4b6a-9f05-b9399ca96dc3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 573, k = 163878 := by
  rw [sum_range_id]
