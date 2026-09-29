-- Prove2me | solution 1 for FiniteTriangular.sum_range_100
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:45:35.224593+00:00
-- url     : https://prove2.me/submissions/e7f78854-4de1-4070-afe2-e634af1e018b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 100, k = 4950 := by
  decide
