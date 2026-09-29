-- Prove2me | solution 1 for FiniteTriangular.sum_range_654
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:55:04.583537+00:00
-- url     : https://prove2.me/submissions/023b9a5d-0d6b-4f2b-8488-a8ff204ba3ce

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 654, k = 213531 := by
  rw [sum_range_id]
