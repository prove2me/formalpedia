-- Prove2me | solution 1 for FiniteTriangular.sum_range_1039
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:47:58.824987+00:00
-- url     : https://prove2.me/submissions/a122a838-4f77-450a-a5e7-1baea622a9c7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1039, k = 539241 := by
  rw [sum_range_id]
