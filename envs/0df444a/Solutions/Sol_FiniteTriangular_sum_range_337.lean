-- Prove2me | solution 1 for FiniteTriangular.sum_range_337
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:36:03.53997+00:00
-- url     : https://prove2.me/submissions/494c49c4-a770-4f72-914a-73586a552b99

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 337, k = 56616 := by
  rw [sum_range_id]
