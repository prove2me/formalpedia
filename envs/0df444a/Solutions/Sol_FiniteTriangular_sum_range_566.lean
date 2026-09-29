-- Prove2me | solution 1 for FiniteTriangular.sum_range_566
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:36:20.252391+00:00
-- url     : https://prove2.me/submissions/a52626d1-abc7-4436-a265-2c9de2197a2e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 566, k = 159895 := by
  rw [sum_range_id]
