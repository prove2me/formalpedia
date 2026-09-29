-- Prove2me | solution 1 for FiniteTriangular.sum_range_47
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:17:22.07203+00:00
-- url     : https://prove2.me/submissions/19e8aa9f-6135-41df-a899-609a6b950013

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 47, k = 1081 := by
  decide
