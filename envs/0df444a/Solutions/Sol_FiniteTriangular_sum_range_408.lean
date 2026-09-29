-- Prove2me | solution 1 for FiniteTriangular.sum_range_408
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:50:35.184571+00:00
-- url     : https://prove2.me/submissions/6213b3ee-4ea0-4672-8c3f-9f80d7ce9ce2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 408, k = 83028 := by
  rw [sum_range_id]
