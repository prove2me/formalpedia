-- Prove2me | solution 1 for FiniteTriangular.sum_range_312
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:22:08.951178+00:00
-- url     : https://prove2.me/submissions/2cbf8ada-835b-4c36-8bd6-bcc15869c5f0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 312, k = 48516 := by
  rw [sum_range_id]
