-- Prove2me | solution 1 for FiniteTriangular.sum_range_308
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:22:06.370282+00:00
-- url     : https://prove2.me/submissions/ce36c3ed-7895-4ba3-89e3-8f007ccde9c0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 308, k = 47278 := by
  rw [sum_range_id]
