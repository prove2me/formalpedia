-- Prove2me | solution 1 for FiniteTriangular.sum_range_708
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:06:58.191649+00:00
-- url     : https://prove2.me/submissions/bb19d4b2-a4ce-4588-ada0-c00349eaaad2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 708, k = 250278 := by
  rw [sum_range_id]
