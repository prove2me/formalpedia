-- Prove2me | solution 1 for FiniteTriangular.sum_range_944
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:57:14.32609+00:00
-- url     : https://prove2.me/submissions/23cb1d9d-2ffa-4ce8-82d7-d1b3e825dd2a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 944, k = 445096 := by
  rw [sum_range_id]
