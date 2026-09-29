-- Prove2me | solution 1 for FiniteTriangular.sum_range_868
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:41:58.916572+00:00
-- url     : https://prove2.me/submissions/a9942b5e-b137-433e-8e7d-a4fc9b5a66ea

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 868, k = 376278 := by
  rw [sum_range_id]
