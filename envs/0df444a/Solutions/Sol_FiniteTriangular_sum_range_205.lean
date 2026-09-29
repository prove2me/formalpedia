-- Prove2me | solution 1 for FiniteTriangular.sum_range_205
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:49:29.443285+00:00
-- url     : https://prove2.me/submissions/0dc82923-9bfb-4b7e-8df3-51a0395ec5aa

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 205, k = 20910 := by
  rw [sum_range_id]
