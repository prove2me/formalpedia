-- Prove2me | solution 1 for FiniteTriangular.sum_range_24
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:08:39.244548+00:00
-- url     : https://prove2.me/submissions/2c0a4741-c2ce-44fe-97c0-fcde7e2d24f6

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 24, k = 276 := by
  decide
