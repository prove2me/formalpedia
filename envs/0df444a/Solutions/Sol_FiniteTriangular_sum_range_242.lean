-- Prove2me | solution 1 for FiniteTriangular.sum_range_242
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:59:23.942288+00:00
-- url     : https://prove2.me/submissions/a43925a2-39fb-4640-916b-d1f1f832d7d0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 242, k = 29161 := by
  rw [sum_range_id]
