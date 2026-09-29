-- Prove2me | solution 1 for FiniteTriangular.sum_range_876
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:43:42.628727+00:00
-- url     : https://prove2.me/submissions/b5892f77-dc61-4d1e-aa9f-60a672d7b091

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 876, k = 383250 := by
  rw [sum_range_id]
