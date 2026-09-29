-- Prove2me | solution 1 for FiniteTriangular.sum_range_361
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:41:21.537577+00:00
-- url     : https://prove2.me/submissions/01015368-10b6-466a-b32e-eeba87fd59ab

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 361, k = 64980 := by
  rw [sum_range_id]
