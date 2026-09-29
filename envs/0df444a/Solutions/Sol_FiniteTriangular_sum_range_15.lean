-- Prove2me | solution 1 for FiniteTriangular.sum_range_15
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:04:10.995519+00:00
-- url     : https://prove2.me/submissions/b3d404ac-92c1-49da-85e2-ed1aefe22fd0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 15, k = 105 := by
  decide
