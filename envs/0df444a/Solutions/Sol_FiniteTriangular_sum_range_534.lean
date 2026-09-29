-- Prove2me | solution 1 for FiniteTriangular.sum_range_534
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:27:31.411557+00:00
-- url     : https://prove2.me/submissions/cf26fea2-246e-4c89-b62d-567ba900c404

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 534, k = 142311 := by
  rw [sum_range_id]
