-- Prove2me | solution 1 for FiniteTriangular.sum_range_230
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:55:14.277599+00:00
-- url     : https://prove2.me/submissions/cfc3ef35-c5a3-4789-b3c4-53ba7c696f4a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 230, k = 26335 := by
  rw [sum_range_id]
