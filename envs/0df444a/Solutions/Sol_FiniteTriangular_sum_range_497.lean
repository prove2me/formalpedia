-- Prove2me | solution 1 for FiniteTriangular.sum_range_497
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:20:33.535632+00:00
-- url     : https://prove2.me/submissions/a93d068f-8f12-48bb-a62f-91cdeb294b41

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 497, k = 123256 := by
  rw [sum_range_id]
