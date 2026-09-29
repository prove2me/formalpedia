-- Prove2me | solution 1 for FiniteTriangular.sum_range_396
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:48:54.236347+00:00
-- url     : https://prove2.me/submissions/f978748a-c91c-4ec5-80d1-df76379f1c15

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 396, k = 78210 := by
  rw [sum_range_id]
