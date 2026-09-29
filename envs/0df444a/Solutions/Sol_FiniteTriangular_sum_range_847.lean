-- Prove2me | solution 1 for FiniteTriangular.sum_range_847
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:36:59.062464+00:00
-- url     : https://prove2.me/submissions/2dcf96e5-4fb6-4486-adfa-f1c5736f94e1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 847, k = 358281 := by
  rw [sum_range_id]
