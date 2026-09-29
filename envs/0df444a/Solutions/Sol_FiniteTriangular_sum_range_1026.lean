-- Prove2me | solution 1 for FiniteTriangular.sum_range_1026
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:45:54.777497+00:00
-- url     : https://prove2.me/submissions/627189d0-271f-42be-8166-51ade6170711

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1026, k = 525825 := by
  rw [sum_range_id]
