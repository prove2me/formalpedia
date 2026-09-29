-- Prove2me | solution 1 for FiniteTriangular.sum_range_225
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:55:11.283405+00:00
-- url     : https://prove2.me/submissions/2183cfab-739f-472a-b9e6-9ef6e7b7c051

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 225, k = 25200 := by
  rw [sum_range_id]
