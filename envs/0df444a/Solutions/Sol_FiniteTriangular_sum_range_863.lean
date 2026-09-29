-- Prove2me | solution 1 for FiniteTriangular.sum_range_863
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:40:13.444908+00:00
-- url     : https://prove2.me/submissions/34db432d-9e9c-45c0-b539-899df821ac28

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 863, k = 371953 := by
  rw [sum_range_id]
