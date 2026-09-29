-- Prove2me | solution 1 for FiniteTriangular.sum_range_332
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:34:18.815961+00:00
-- url     : https://prove2.me/submissions/4e3385d3-9c5d-45be-a52d-205028e94305

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 332, k = 54946 := by
  rw [sum_range_id]
