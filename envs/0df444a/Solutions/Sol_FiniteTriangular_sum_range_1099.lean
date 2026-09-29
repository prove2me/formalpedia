-- Prove2me | solution 1 for FiniteTriangular.sum_range_1099
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:25:41.548726+00:00
-- url     : https://prove2.me/submissions/8f79fb81-4d16-43a4-a88a-169c0a531e39

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1099, k = 603351 := by
  rw [sum_range_id]
