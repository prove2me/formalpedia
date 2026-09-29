-- Prove2me | solution 1 for FiniteTriangular.sum_range_330
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:34:17.514847+00:00
-- url     : https://prove2.me/submissions/bd4b7715-b026-4698-a7fd-d326cc8744fc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 330, k = 54285 := by
  rw [sum_range_id]
