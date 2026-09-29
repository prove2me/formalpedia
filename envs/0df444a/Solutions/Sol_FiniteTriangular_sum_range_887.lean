-- Prove2me | solution 1 for FiniteTriangular.sum_range_887
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:45:20.947749+00:00
-- url     : https://prove2.me/submissions/850379a4-c996-4856-a8b3-2f87fd75aea9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 887, k = 392941 := by
  rw [sum_range_id]
