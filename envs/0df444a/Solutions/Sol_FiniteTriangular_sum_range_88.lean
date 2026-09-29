-- Prove2me | solution 1 for FiniteTriangular.sum_range_88
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:40:19.395991+00:00
-- url     : https://prove2.me/submissions/7eca12e6-4d8c-44b4-a165-d7bbcce5152d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 88, k = 3828 := by
  decide
