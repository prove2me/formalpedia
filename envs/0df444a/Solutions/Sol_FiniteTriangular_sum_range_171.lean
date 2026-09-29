-- Prove2me | solution 1 for FiniteTriangular.sum_range_171
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:20:44.259825+00:00
-- url     : https://prove2.me/submissions/df00a56b-58ac-4514-9cbb-7ef81b329b1f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 171, k = 14535 := by
  rw [sum_range_id]
