-- Prove2me | solution 1 for FiniteTriangular.sum_range_883
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:45:18.371533+00:00
-- url     : https://prove2.me/submissions/b88785bb-74ad-441f-8484-3b6497ad0f0b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 883, k = 389403 := by
  rw [sum_range_id]
