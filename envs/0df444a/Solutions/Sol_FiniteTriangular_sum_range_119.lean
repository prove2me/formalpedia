-- Prove2me | solution 1 for FiniteTriangular.sum_range_119
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:49:22.354987+00:00
-- url     : https://prove2.me/submissions/dd0d4b7e-f628-4d3a-85cc-b2bda7d9cb69

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 119, k = 7021 := by
  decide
