-- Prove2me | solution 1 for FiniteTriangular.sum_range_1064
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:17:05.558932+00:00
-- url     : https://prove2.me/submissions/f9cb0878-613a-4fe0-bc56-851ffcbd193d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1064, k = 565516 := by
  rw [sum_range_id]
