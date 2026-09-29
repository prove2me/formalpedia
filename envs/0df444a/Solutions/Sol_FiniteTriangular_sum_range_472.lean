-- Prove2me | solution 1 for FiniteTriangular.sum_range_472
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:13:53.329181+00:00
-- url     : https://prove2.me/submissions/9b8b5c77-5f57-42be-8e46-585ccacb044a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 472, k = 111156 := by
  rw [sum_range_id]
