-- Prove2me | solution 1 for FiniteTriangular.sum_range_1077
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:20:32.863526+00:00
-- url     : https://prove2.me/submissions/92297898-b325-41e2-97d6-8870f81fdf42

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1077, k = 579426 := by
  rw [sum_range_id]
