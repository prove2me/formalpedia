-- Prove2me | solution 1 for FiniteTriangular.sum_range_287
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:16:44.504249+00:00
-- url     : https://prove2.me/submissions/b1a0b769-e818-4bf6-b72b-cb8d059e619d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 287, k = 41041 := by
  rw [sum_range_id]
