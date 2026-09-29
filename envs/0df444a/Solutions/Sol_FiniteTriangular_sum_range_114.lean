-- Prove2me | solution 1 for FiniteTriangular.sum_range_114
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:49:17.717891+00:00
-- url     : https://prove2.me/submissions/5d964c06-773e-4723-90ef-9c9330825d03

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 114, k = 6441 := by
  decide
