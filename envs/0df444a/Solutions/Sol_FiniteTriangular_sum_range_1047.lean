-- Prove2me | solution 1 for FiniteTriangular.sum_range_1047
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:13:20.621695+00:00
-- url     : https://prove2.me/submissions/c72aac15-8662-402e-bca4-e3e1c2b93545

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1047, k = 547581 := by
  rw [sum_range_id]
