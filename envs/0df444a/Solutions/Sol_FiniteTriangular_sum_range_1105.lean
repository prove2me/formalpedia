-- Prove2me | solution 1 for FiniteTriangular.sum_range_1105
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:27:30.582025+00:00
-- url     : https://prove2.me/submissions/99641d6e-c3b3-4f98-a186-9b2be822c073

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1105, k = 609960 := by
  rw [sum_range_id]
