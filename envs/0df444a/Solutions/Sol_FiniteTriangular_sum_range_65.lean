-- Prove2me | solution 1 for FiniteTriangular.sum_range_65
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:33:00.012148+00:00
-- url     : https://prove2.me/submissions/d264f876-e6bc-49a5-ba87-6fabdf97b6da

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 65, k = 2080 := by
  decide
