-- Prove2me | solution 1 for FiniteTriangular.sum_range_471
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:13:52.724287+00:00
-- url     : https://prove2.me/submissions/317690b3-5e8b-44bc-9e79-9fa55adb57f7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 471, k = 110685 := by
  rw [sum_range_id]
