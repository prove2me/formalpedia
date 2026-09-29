-- Prove2me | solution 1 for FiniteTriangular.sum_range_23
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:08:38.606092+00:00
-- url     : https://prove2.me/submissions/8e366f0d-3682-45d2-b73b-064223d9f3cc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 23, k = 253 := by
  decide
