-- Prove2me | solution 1 for FiniteTriangular.sum_range_290
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:18:18.077561+00:00
-- url     : https://prove2.me/submissions/42c8474f-96c8-450e-a03e-e3cf54033d9d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 290, k = 41905 := by
  rw [sum_range_id]
