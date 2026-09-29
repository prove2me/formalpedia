-- Prove2me | solution 1 for FiniteTriangular.sum_range_96
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:43:54.654691+00:00
-- url     : https://prove2.me/submissions/310f3a8b-da17-44fa-a421-b30007583dc1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 96, k = 4560 := by
  decide
