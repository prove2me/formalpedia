-- Prove2me | solution 1 for FiniteTriangular.sum_range_711
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:07:00.189588+00:00
-- url     : https://prove2.me/submissions/da850d0e-49da-4601-a3d7-5424d625593f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 711, k = 252405 := by
  rw [sum_range_id]
