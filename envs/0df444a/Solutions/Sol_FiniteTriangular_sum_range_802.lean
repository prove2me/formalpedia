-- Prove2me | solution 1 for FiniteTriangular.sum_range_802
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:28:28.787199+00:00
-- url     : https://prove2.me/submissions/2b2336d5-5c0b-4017-b563-8de925830665

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 802, k = 321201 := by
  rw [sum_range_id]
