-- Prove2me | solution 1 for FiniteTriangular.sum_range_556
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:34:26.381695+00:00
-- url     : https://prove2.me/submissions/32d73dc1-7a5c-44c7-8794-dbc8638e7c7a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 556, k = 154290 := by
  rw [sum_range_id]
