-- Prove2me | solution 1 for FiniteTriangular.sum_range_58
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:21:34.23236+00:00
-- url     : https://prove2.me/submissions/162393fc-65cc-4458-8bb2-2e3de0c5516b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 58, k = 1653 := by
  decide
