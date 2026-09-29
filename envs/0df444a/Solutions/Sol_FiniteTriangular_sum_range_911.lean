-- Prove2me | solution 1 for FiniteTriangular.sum_range_911
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:50:24.744754+00:00
-- url     : https://prove2.me/submissions/afbbeea1-e8d2-4593-8437-5a7960d85964

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 911, k = 414505 := by
  rw [sum_range_id]
