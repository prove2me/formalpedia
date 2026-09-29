-- Prove2me | solution 1 for FiniteTriangular.sum_range_710
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:06:59.628303+00:00
-- url     : https://prove2.me/submissions/1f262ceb-7591-460a-8c12-9622d93fefc0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 710, k = 251695 := by
  rw [sum_range_id]
