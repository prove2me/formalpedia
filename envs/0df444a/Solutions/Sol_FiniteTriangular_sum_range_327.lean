-- Prove2me | solution 1 for FiniteTriangular.sum_range_327
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:32:33.925427+00:00
-- url     : https://prove2.me/submissions/8c103ec8-741e-48d4-9023-de7ea252cf74

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 327, k = 53301 := by
  rw [sum_range_id]
