-- Prove2me | solution 1 for FiniteTriangular.sum_range_1123
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:30:42.081848+00:00
-- url     : https://prove2.me/submissions/7de2e292-7b90-4b3e-9690-7ebcc48af762

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1123, k = 630003 := by
  rw [sum_range_id]
