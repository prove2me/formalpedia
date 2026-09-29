-- Prove2me | solution 1 for FiniteTriangular.sum_range_651
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:55:02.301419+00:00
-- url     : https://prove2.me/submissions/a7933910-e0c8-4f01-a4bd-344bf1897faf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 651, k = 211575 := by
  rw [sum_range_id]
