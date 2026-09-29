-- Prove2me | solution 1 for FiniteTriangular.sum_range_754
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:18:11.67777+00:00
-- url     : https://prove2.me/submissions/447d69cb-66b7-4dbd-81eb-2815163ebda6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 754, k = 283881 := by
  rw [sum_range_id]
