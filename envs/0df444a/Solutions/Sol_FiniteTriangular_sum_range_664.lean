-- Prove2me | solution 1 for FiniteTriangular.sum_range_664
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:56:51.135291+00:00
-- url     : https://prove2.me/submissions/38f62b36-6558-46e3-b9ed-1a7e7b96de58

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 664, k = 220116 := by
  rw [sum_range_id]
