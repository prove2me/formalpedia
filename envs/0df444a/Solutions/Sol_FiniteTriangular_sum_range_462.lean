-- Prove2me | solution 1 for FiniteTriangular.sum_range_462
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:12:05.326539+00:00
-- url     : https://prove2.me/submissions/e99e42c0-be95-4f4d-88ba-8e4aae821807

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 462, k = 106491 := by
  rw [sum_range_id]
