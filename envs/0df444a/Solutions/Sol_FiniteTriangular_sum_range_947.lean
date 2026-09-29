-- Prove2me | solution 1 for FiniteTriangular.sum_range_947
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:59:07.799213+00:00
-- url     : https://prove2.me/submissions/5fc5f1e2-1a02-499c-bf25-721b558bdb17

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 947, k = 447931 := by
  rw [sum_range_id]
