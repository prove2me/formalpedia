-- Prove2me | solution 1 for FiniteTriangular.sum_range_202
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:49:27.342551+00:00
-- url     : https://prove2.me/submissions/de15c531-23cc-4fa8-9d10-44be6240e9d2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 202, k = 20301 := by
  rw [sum_range_id]
