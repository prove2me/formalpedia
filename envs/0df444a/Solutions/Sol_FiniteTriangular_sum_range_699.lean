-- Prove2me | solution 1 for FiniteTriangular.sum_range_699
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:05:10.817759+00:00
-- url     : https://prove2.me/submissions/906eda46-a7a6-4827-ac22-9d7c13c146ec

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 699, k = 243951 := by
  rw [sum_range_id]
