-- Prove2me | solution 1 for FiniteTriangular.sum_range_865
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:41:57.015704+00:00
-- url     : https://prove2.me/submissions/088aa010-3f77-434c-9f46-d979a7c23a1a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 865, k = 373680 := by
  rw [sum_range_id]
