-- Prove2me | solution 1 for FiniteTriangular.sum_range_753
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:18:11.01638+00:00
-- url     : https://prove2.me/submissions/924a79de-c852-463d-9718-29be7ae70da6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 753, k = 283128 := by
  rw [sum_range_id]
