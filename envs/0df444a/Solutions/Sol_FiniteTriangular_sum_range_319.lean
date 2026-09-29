-- Prove2me | solution 1 for FiniteTriangular.sum_range_319
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:30:38.067596+00:00
-- url     : https://prove2.me/submissions/8ebb3f96-6dda-4702-aede-634d2e4702de

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 319, k = 50721 := by
  rw [sum_range_id]
