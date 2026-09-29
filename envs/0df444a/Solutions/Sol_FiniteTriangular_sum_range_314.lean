-- Prove2me | solution 1 for FiniteTriangular.sum_range_314
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:30:34.702049+00:00
-- url     : https://prove2.me/submissions/9859abb8-0832-4599-8f87-b20f5d3e038f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 314, k = 49141 := by
  rw [sum_range_id]
