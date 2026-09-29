-- Prove2me | solution 1 for FiniteTriangular.sum_range_458
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:12:02.545798+00:00
-- url     : https://prove2.me/submissions/311d3ecd-3b62-4293-b59b-dd42238e5e3e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 458, k = 104653 := by
  rw [sum_range_id]
