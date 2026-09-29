-- Prove2me | solution 1 for FiniteTriangular.sum_range_791
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:25:09.206599+00:00
-- url     : https://prove2.me/submissions/23f78b3d-70cd-4e45-af67-2973f6f96b5f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 791, k = 312445 := by
  rw [sum_range_id]
