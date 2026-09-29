-- Prove2me | solution 1 for FiniteTriangular.sum_range_1081
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:22:25.260223+00:00
-- url     : https://prove2.me/submissions/263fc06d-b83d-4028-8209-7b494345c4f2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1081, k = 583740 := by
  rw [sum_range_id]
