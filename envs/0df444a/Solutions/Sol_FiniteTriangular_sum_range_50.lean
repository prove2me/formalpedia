-- Prove2me | solution 1 for FiniteTriangular.sum_range_50
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:19:10.129975+00:00
-- url     : https://prove2.me/submissions/b38e2f76-1fca-4ed0-a0f3-b9502ffc4df4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 50, k = 1225 := by
  decide
