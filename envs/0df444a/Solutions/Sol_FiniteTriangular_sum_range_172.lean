-- Prove2me | solution 1 for FiniteTriangular.sum_range_172
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:22:16.220406+00:00
-- url     : https://prove2.me/submissions/3f02a93f-0f0b-4bfd-937f-91e1112e7217

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 172, k = 14706 := by
  rw [sum_range_id]
