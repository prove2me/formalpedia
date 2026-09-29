-- Prove2me | solution 1 for FiniteTriangular.sum_range_73
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:38:18.354779+00:00
-- url     : https://prove2.me/submissions/02487f69-1e86-4a84-bae3-02435847728e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 73, k = 2628 := by
  decide
