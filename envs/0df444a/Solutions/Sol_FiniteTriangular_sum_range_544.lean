-- Prove2me | solution 1 for FiniteTriangular.sum_range_544
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:29:09.647535+00:00
-- url     : https://prove2.me/submissions/b0cbc0f0-d19e-4052-92c7-ebf84e6b21ec

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 544, k = 147696 := by
  rw [sum_range_id]
