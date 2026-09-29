-- Prove2me | solution 1 for FiniteTriangular.sum_range_500
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:20:35.234962+00:00
-- url     : https://prove2.me/submissions/15157a74-7cd6-4585-81d8-8a91c355c093

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 500, k = 124750 := by
  rw [sum_range_id]
