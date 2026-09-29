-- Prove2me | solution 1 for FiniteTriangular.sum_range_521
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:25:50.622296+00:00
-- url     : https://prove2.me/submissions/1ab91e83-0727-4695-8dac-7060b1601b92

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 521, k = 135460 := by
  rw [sum_range_id]
