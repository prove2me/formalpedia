-- Prove2me | solution 1 for FiniteTriangular.sum_range_300
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:20:06.137024+00:00
-- url     : https://prove2.me/submissions/68ea5341-5bda-4bf9-bb97-152ee09fac27

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 300, k = 44850 := by
  rw [sum_range_id]
