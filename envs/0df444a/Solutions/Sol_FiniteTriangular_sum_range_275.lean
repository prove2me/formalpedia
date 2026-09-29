-- Prove2me | solution 1 for FiniteTriangular.sum_range_275
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:14:53.644281+00:00
-- url     : https://prove2.me/submissions/df452d95-4409-4f23-a28a-6387dfd65b8d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 275, k = 37675 := by
  rw [sum_range_id]
