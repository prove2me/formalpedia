-- Prove2me | solution 1 for FiniteTriangular.sum_range_746
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:16:31.155608+00:00
-- url     : https://prove2.me/submissions/b6ed6480-7c70-4f0a-a8d2-6afa6724469d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 746, k = 277885 := by
  rw [sum_range_id]
