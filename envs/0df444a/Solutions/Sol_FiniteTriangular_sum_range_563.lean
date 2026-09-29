-- Prove2me | solution 1 for FiniteTriangular.sum_range_563
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:36:18.060872+00:00
-- url     : https://prove2.me/submissions/9baffad4-ea29-4952-8cf4-6180aedc4685

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 563, k = 158203 := by
  rw [sum_range_id]
