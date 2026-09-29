-- Prove2me | solution 1 for FiniteTriangular.sum_range_912
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:50:25.381926+00:00
-- url     : https://prove2.me/submissions/c8f95f90-77b5-45b9-b0b5-2b89c1b1c8ea

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 912, k = 415416 := by
  rw [sum_range_id]
