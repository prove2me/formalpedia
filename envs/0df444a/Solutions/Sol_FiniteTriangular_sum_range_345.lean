-- Prove2me | solution 1 for FiniteTriangular.sum_range_345
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:37:48.397053+00:00
-- url     : https://prove2.me/submissions/7d40d0c1-5858-4877-8e80-8edb561d4844

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 345, k = 59340 := by
  rw [sum_range_id]
