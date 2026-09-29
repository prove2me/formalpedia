-- Prove2me | solution 1 for FiniteTriangular.sum_range_838
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:35:22.615479+00:00
-- url     : https://prove2.me/submissions/cf8a0a47-405c-49ae-8645-c759266dfc48

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 838, k = 350703 := by
  rw [sum_range_id]
