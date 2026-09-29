-- Prove2me | solution 1 for FiniteTriangular.sum_range_511
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:22:23.762015+00:00
-- url     : https://prove2.me/submissions/dd5072fb-362d-4e3f-b03a-53da667feb8f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 511, k = 130305 := by
  rw [sum_range_id]
