-- Prove2me | solution 1 for FiniteTriangular.sum_range_560
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:34:28.66215+00:00
-- url     : https://prove2.me/submissions/028f4731-2e0f-4cbc-b267-b809924b0bfc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 560, k = 156520 := by
  rw [sum_range_id]
