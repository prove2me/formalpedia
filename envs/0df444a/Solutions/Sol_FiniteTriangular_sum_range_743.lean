-- Prove2me | solution 1 for FiniteTriangular.sum_range_743
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:14:45.688484+00:00
-- url     : https://prove2.me/submissions/933c83cb-e3a1-47c8-9965-2c251f0d774d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 743, k = 275653 := by
  rw [sum_range_id]
