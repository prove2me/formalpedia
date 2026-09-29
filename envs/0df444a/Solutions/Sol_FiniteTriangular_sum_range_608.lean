-- Prove2me | solution 1 for FiniteTriangular.sum_range_608
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:44:57.615553+00:00
-- url     : https://prove2.me/submissions/5b59ff16-df3f-4333-9837-7880db20f7c2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 608, k = 184528 := by
  rw [sum_range_id]
