-- Prove2me | solution 1 for FiniteTriangular.sum_range_398
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:48:55.367989+00:00
-- url     : https://prove2.me/submissions/3c776fac-b6bb-4941-9cc4-a059b0d07fa4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 398, k = 79003 := by
  rw [sum_range_id]
