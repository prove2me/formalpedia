-- Prove2me | solution 1 for FiniteTriangular.sum_range_646
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:53:26.914299+00:00
-- url     : https://prove2.me/submissions/abc3bb33-9e52-4e15-aade-a27c92f72784

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 646, k = 208335 := by
  rw [sum_range_id]
