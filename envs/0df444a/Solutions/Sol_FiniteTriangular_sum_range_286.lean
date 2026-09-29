-- Prove2me | solution 1 for FiniteTriangular.sum_range_286
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:16:43.939789+00:00
-- url     : https://prove2.me/submissions/8ab2e09c-77aa-4e0e-a145-dd1182384a23

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 286, k = 40755 := by
  rw [sum_range_id]
