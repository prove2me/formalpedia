-- Prove2me | solution 1 for FiniteTriangular.sum_range_1037
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:47:57.398973+00:00
-- url     : https://prove2.me/submissions/c4449ba9-b179-43c1-ae7b-0df73ca7f9ad

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1037, k = 537166 := by
  rw [sum_range_id]
