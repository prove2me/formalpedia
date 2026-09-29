-- Prove2me | solution 1 for FiniteTriangular.sum_range_51
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:19:10.889018+00:00
-- url     : https://prove2.me/submissions/e5c04110-38cf-4081-aeb0-4a85c638641d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 51, k = 1275 := by
  decide
