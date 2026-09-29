-- Prove2me | solution 1 for FiniteTriangular.sum_range_945
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:59:06.501064+00:00
-- url     : https://prove2.me/submissions/bedb2f83-8883-4f9b-a9fe-da1f0e12f692

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 945, k = 446040 := by
  rw [sum_range_id]
