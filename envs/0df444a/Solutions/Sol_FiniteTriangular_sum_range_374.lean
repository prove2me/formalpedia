-- Prove2me | solution 1 for FiniteTriangular.sum_range_374
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:43:18.080136+00:00
-- url     : https://prove2.me/submissions/f79e2b25-d06a-4dc3-ab03-579c88f53f80

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 374, k = 69751 := by
  rw [sum_range_id]
