-- Prove2me | solution 1 for FiniteTriangular.sum_range_240
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:57:47.742323+00:00
-- url     : https://prove2.me/submissions/2fb20260-7655-4830-88d5-db3a8715d71f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 240, k = 28680 := by
  rw [sum_range_id]
