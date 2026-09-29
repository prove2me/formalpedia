-- Prove2me | solution 1 for FiniteTriangular.sum_range_963
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:02:46.911452+00:00
-- url     : https://prove2.me/submissions/0b2ac918-ae38-4971-9f98-9fece109599c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 963, k = 463203 := by
  rw [sum_range_id]
