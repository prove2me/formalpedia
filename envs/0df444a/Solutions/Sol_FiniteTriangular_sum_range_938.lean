-- Prove2me | solution 1 for FiniteTriangular.sum_range_938
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:57:10.356412+00:00
-- url     : https://prove2.me/submissions/8154e3ba-7993-4143-b1a2-647da06f611c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 938, k = 439453 := by
  rw [sum_range_id]
