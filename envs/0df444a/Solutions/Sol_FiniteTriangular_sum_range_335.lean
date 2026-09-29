-- Prove2me | solution 1 for FiniteTriangular.sum_range_335
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:34:20.875427+00:00
-- url     : https://prove2.me/submissions/566ef89b-0658-4b65-8747-71f01d677a5b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 335, k = 55945 := by
  rw [sum_range_id]
