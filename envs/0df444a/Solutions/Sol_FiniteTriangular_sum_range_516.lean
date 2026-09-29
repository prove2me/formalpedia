-- Prove2me | solution 1 for FiniteTriangular.sum_range_516
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:24:06.872149+00:00
-- url     : https://prove2.me/submissions/c75b4789-df75-4839-9187-1479c083089a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 516, k = 132870 := by
  rw [sum_range_id]
