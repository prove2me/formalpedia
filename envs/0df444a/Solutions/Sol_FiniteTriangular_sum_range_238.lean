-- Prove2me | solution 1 for FiniteTriangular.sum_range_238
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:57:46.494259+00:00
-- url     : https://prove2.me/submissions/35282b70-4bd0-4a9c-ab40-a47a56aeb0af

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 238, k = 28203 := by
  rw [sum_range_id]
