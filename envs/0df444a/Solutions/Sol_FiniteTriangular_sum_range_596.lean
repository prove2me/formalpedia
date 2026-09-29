-- Prove2me | solution 1 for FiniteTriangular.sum_range_596
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:43:10.090576+00:00
-- url     : https://prove2.me/submissions/4b4aca59-fe65-476b-9a4c-3b2aae39aa42

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 596, k = 177310 := by
  rw [sum_range_id]
