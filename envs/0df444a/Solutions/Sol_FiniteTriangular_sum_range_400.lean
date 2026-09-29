-- Prove2me | solution 1 for FiniteTriangular.sum_range_400
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:48:56.490927+00:00
-- url     : https://prove2.me/submissions/f3196d00-e154-461a-a2cb-8ec9472c7a93

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 400, k = 79800 := by
  rw [sum_range_id]
