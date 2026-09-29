-- Prove2me | solution 1 for FiniteTriangular.sum_range_707
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:06:57.583627+00:00
-- url     : https://prove2.me/submissions/33b3df6b-7205-47aa-8782-2a27b2f723c3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 707, k = 249571 := by
  rw [sum_range_id]
