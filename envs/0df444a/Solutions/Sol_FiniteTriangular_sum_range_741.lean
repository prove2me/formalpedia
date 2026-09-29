-- Prove2me | solution 1 for FiniteTriangular.sum_range_741
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:14:44.512278+00:00
-- url     : https://prove2.me/submissions/456c8be3-112a-4e8a-a23f-2c2110ca9420

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 741, k = 274170 := by
  rw [sum_range_id]
