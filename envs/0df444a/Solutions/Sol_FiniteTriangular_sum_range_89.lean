-- Prove2me | solution 1 for FiniteTriangular.sum_range_89
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:43:50.082004+00:00
-- url     : https://prove2.me/submissions/e619e2c4-dd6d-4f7f-8cc2-315104ef8471

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 89, k = 3916 := by
  decide
