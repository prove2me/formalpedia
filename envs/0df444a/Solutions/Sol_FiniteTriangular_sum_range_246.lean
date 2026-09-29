-- Prove2me | solution 1 for FiniteTriangular.sum_range_246
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:59:26.483974+00:00
-- url     : https://prove2.me/submissions/fd4ec459-6bb2-4684-bb8b-184167be0f60

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 246, k = 30135 := by
  rw [sum_range_id]
