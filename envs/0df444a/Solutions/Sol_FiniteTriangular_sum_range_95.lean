-- Prove2me | solution 1 for FiniteTriangular.sum_range_95
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:43:54.003413+00:00
-- url     : https://prove2.me/submissions/c5c45651-c683-4c5e-925a-9c39165e1f0e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 95, k = 4465 := by
  decide
