-- Prove2me | solution 1 for FiniteTriangular.sum_range_1124
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:30:42.824671+00:00
-- url     : https://prove2.me/submissions/7077eda3-3c5e-4335-a547-9949028b4528

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1124, k = 631126 := by
  rw [sum_range_id]
