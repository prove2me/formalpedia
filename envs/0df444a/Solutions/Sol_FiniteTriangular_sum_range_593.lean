-- Prove2me | solution 1 for FiniteTriangular.sum_range_593
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:43:08.413116+00:00
-- url     : https://prove2.me/submissions/38912be2-6a06-4d29-9958-113d94bdf7e7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 593, k = 175528 := by
  rw [sum_range_id]
