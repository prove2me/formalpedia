-- Prove2me | solution 1 for FiniteTriangular.sum_range_842
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:36:55.991596+00:00
-- url     : https://prove2.me/submissions/b6d2e477-35da-4b5e-b89c-66730729255a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 842, k = 354061 := by
  rw [sum_range_id]
