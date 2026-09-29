-- Prove2me | solution 1 for FiniteTriangular.sum_range_616
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:46:46.088496+00:00
-- url     : https://prove2.me/submissions/20cfe791-9b21-43d3-9dfd-bc7b06d2df9f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 616, k = 189420 := by
  rw [sum_range_id]
