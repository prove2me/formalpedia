-- Prove2me | solution 1 for FiniteTriangular.sum_range_200
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:47:35.879989+00:00
-- url     : https://prove2.me/submissions/aff284fe-ef7f-477d-8b5a-57e927945252

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 200, k = 19900 := by
  rw [sum_range_id]
