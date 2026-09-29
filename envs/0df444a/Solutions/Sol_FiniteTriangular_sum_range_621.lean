-- Prove2me | solution 1 for FiniteTriangular.sum_range_621
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:48:20.9767+00:00
-- url     : https://prove2.me/submissions/5719c086-f8cc-4de3-a301-3fc1333f5ee7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 621, k = 192510 := by
  rw [sum_range_id]
