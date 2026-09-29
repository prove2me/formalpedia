-- Prove2me | solution 1 for FiniteTriangular.sum_range_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:00:58.101984+00:00
-- url     : https://prove2.me/submissions/ac807584-7e21-47e9-ab5e-5ecaec84ec0c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1, k = 0 := by
  decide
