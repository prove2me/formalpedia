-- Prove2me | solution 1 for FiniteTriangular.sum_range_108
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:47:25.082621+00:00
-- url     : https://prove2.me/submissions/2e334e10-2cf0-4ed7-b0c3-0c55fdcdeb67

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 108, k = 5778 := by
  decide
