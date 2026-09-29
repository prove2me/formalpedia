-- Prove2me | solution 1 for FiniteTriangular.sum_range_133
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:14:46.309888+00:00
-- url     : https://prove2.me/submissions/2579e0d3-b344-4a85-a3bb-503c64a358e4

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 133, k = 8778 := by
  rw [sum_range_id]
