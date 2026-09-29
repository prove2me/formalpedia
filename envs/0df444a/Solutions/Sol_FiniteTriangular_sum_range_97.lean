-- Prove2me | solution 1 for FiniteTriangular.sum_range_97
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:45:32.01345+00:00
-- url     : https://prove2.me/submissions/eb057fa9-213b-49f7-8c80-f606002dd04d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 97, k = 4656 := by
  decide
