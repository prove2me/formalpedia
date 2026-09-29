-- Prove2me | solution 1 for FiniteTriangular.sum_range_766
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:19:51.93366+00:00
-- url     : https://prove2.me/submissions/811486fb-8844-4979-919f-27132feeeda3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 766, k = 292995 := by
  rw [sum_range_id]
