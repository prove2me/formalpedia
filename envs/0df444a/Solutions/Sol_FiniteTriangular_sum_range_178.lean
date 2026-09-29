-- Prove2me | solution 1 for FiniteTriangular.sum_range_178
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:22:21.2546+00:00
-- url     : https://prove2.me/submissions/80665667-64d4-439a-a3ab-c13c0cd93f34

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 178, k = 15753 := by
  rw [sum_range_id]
