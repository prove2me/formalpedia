-- Prove2me | solution 1 for FiniteTriangular.sum_range_98
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:45:32.734464+00:00
-- url     : https://prove2.me/submissions/201fcfee-48fa-4a71-b5f2-c2e4094c6326

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 98, k = 4753 := by
  decide
