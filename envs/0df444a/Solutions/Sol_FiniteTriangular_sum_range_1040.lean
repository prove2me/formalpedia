-- Prove2me | solution 1 for FiniteTriangular.sum_range_1040
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:47:59.512987+00:00
-- url     : https://prove2.me/submissions/5e354f6e-1285-47a9-9f51-7107751a1de3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1040, k = 540280 := by
  rw [sum_range_id]
