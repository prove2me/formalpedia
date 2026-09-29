-- Prove2me | solution 1 for FiniteTriangular.sum_range_279
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:14:56.148178+00:00
-- url     : https://prove2.me/submissions/e7aa8ee7-1cc0-43fa-b3cf-a0d4290e1be8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 279, k = 38781 := by
  rw [sum_range_id]
