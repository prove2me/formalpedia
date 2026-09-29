-- Prove2me | solution 1 for FiniteTriangular.sum_range_558
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:34:27.530303+00:00
-- url     : https://prove2.me/submissions/108ca9d5-22cb-42aa-a582-fcba23fa9644

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 558, k = 155403 := by
  rw [sum_range_id]
