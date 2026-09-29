-- Prove2me | solution 1 for FiniteTriangular.sum_range_271
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:13:02.090325+00:00
-- url     : https://prove2.me/submissions/26e51817-cb07-4620-ad15-3fe525d36012

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 271, k = 36585 := by
  rw [sum_range_id]
