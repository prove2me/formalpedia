-- Prove2me | solution 1 for FiniteTriangular.sum_range_919
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:52:01.65932+00:00
-- url     : https://prove2.me/submissions/ed6d4da7-4ce3-44c2-90ad-b7f52bf83144

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 919, k = 421821 := by
  rw [sum_range_id]
