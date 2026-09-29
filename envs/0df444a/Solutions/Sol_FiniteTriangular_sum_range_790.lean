-- Prove2me | solution 1 for FiniteTriangular.sum_range_790
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:25:08.6214+00:00
-- url     : https://prove2.me/submissions/9014502a-8df1-4aee-9b69-ed58d14efce5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 790, k = 311655 := by
  rw [sum_range_id]
