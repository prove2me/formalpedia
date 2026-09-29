-- Prove2me | solution 1 for FiniteTriangular.sum_range_354
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:39:27.073327+00:00
-- url     : https://prove2.me/submissions/780bc1c1-04d8-44e2-a680-27fce33ac942

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 354, k = 62481 := by
  rw [sum_range_id]
