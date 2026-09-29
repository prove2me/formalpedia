-- Prove2me | solution 1 for FiniteTriangular.sum_range_935
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:55:35.613399+00:00
-- url     : https://prove2.me/submissions/bc97f845-8638-41fa-8fd9-ae4d8c1e80c7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 935, k = 436645 := by
  rw [sum_range_id]
