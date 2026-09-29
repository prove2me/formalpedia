-- Prove2me | solution 1 for FiniteTriangular.sum_range_966
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:02:49.088915+00:00
-- url     : https://prove2.me/submissions/acbfcada-d6d1-4ce8-95f4-c5308736c45b

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 966, k = 466095 := by
  rw [sum_range_id]
