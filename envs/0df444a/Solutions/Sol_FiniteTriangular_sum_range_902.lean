-- Prove2me | solution 1 for FiniteTriangular.sum_range_902
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:48:46.037859+00:00
-- url     : https://prove2.me/submissions/bbee7b0b-8606-410d-85a7-a9e17fd5ee45

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 902, k = 406351 := by
  rw [sum_range_id]
