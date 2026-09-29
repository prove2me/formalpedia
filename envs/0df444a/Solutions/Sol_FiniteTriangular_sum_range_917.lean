-- Prove2me | solution 1 for FiniteTriangular.sum_range_917
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:52:00.458404+00:00
-- url     : https://prove2.me/submissions/e85d7375-7a9f-4f46-a325-6dbb83cdff41

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 917, k = 419986 := by
  rw [sum_range_id]
