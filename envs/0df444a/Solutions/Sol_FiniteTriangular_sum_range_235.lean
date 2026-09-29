-- Prove2me | solution 1 for FiniteTriangular.sum_range_235
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:57:44.642234+00:00
-- url     : https://prove2.me/submissions/cb56a23e-909f-4ab4-a0f5-ad8510f1acd2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 235, k = 27495 := by
  rw [sum_range_id]
