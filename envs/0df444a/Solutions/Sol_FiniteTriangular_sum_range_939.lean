-- Prove2me | solution 1 for FiniteTriangular.sum_range_939
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:57:10.967025+00:00
-- url     : https://prove2.me/submissions/beaf6515-8320-4d0a-9e42-4d2ae334fb61

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 939, k = 440391 := by
  rw [sum_range_id]
