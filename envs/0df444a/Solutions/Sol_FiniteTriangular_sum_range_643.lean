-- Prove2me | solution 1 for FiniteTriangular.sum_range_643
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:53:25.15773+00:00
-- url     : https://prove2.me/submissions/82ac51c4-5ea7-4ef6-8253-ea4fb4aa4d52

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 643, k = 206403 := by
  rw [sum_range_id]
