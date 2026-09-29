-- Prove2me | solution 1 for FiniteTriangular.sum_range_420
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:54:04.222154+00:00
-- url     : https://prove2.me/submissions/d60c125d-778c-481a-b01f-51b33ed39376

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 420, k = 87990 := by
  rw [sum_range_id]
