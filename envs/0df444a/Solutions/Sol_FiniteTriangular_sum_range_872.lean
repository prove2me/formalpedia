-- Prove2me | solution 1 for FiniteTriangular.sum_range_872
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:42:01.392255+00:00
-- url     : https://prove2.me/submissions/6277c4a6-c828-4186-b44c-f56c7c244133

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 872, k = 379756 := by
  rw [sum_range_id]
