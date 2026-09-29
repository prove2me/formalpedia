-- Prove2me | solution 1 for FiniteTriangular.sum_range_584
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:39:51.273605+00:00
-- url     : https://prove2.me/submissions/3f0875d2-8ca6-481c-8878-5fae57273acf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 584, k = 170236 := by
  rw [sum_range_id]
