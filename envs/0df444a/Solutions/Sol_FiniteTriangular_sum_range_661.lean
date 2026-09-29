-- Prove2me | solution 1 for FiniteTriangular.sum_range_661
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:56:49.251016+00:00
-- url     : https://prove2.me/submissions/f04f5970-8b90-471b-8156-2e16a1bc1949

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 661, k = 218130 := by
  rw [sum_range_id]
