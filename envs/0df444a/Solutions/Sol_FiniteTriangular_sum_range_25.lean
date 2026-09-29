-- Prove2me | solution 1 for FiniteTriangular.sum_range_25
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:08:39.975976+00:00
-- url     : https://prove2.me/submissions/0bc3a0eb-0221-402c-8cd6-416a06a39e97

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 25, k = 300 := by
  decide
