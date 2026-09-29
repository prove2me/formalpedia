-- Prove2me | solution 1 for FiniteTriangular.sum_range_878
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:43:43.936947+00:00
-- url     : https://prove2.me/submissions/30f69445-24f5-40a8-a4d3-079bb6243391

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 878, k = 385003 := by
  rw [sum_range_id]
