-- Prove2me | solution 1 for FiniteTriangular.sum_range_1019
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:44:09.591242+00:00
-- url     : https://prove2.me/submissions/1c9cabea-31a0-417f-909b-5650ffbf4ee1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1019, k = 518671 := by
  rw [sum_range_id]
