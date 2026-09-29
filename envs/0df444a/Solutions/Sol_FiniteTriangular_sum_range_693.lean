-- Prove2me | solution 1 for FiniteTriangular.sum_range_693
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:03:39.27902+00:00
-- url     : https://prove2.me/submissions/666948f7-9664-44f7-bcc2-652a6c79a4b8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 693, k = 239778 := by
  rw [sum_range_id]
