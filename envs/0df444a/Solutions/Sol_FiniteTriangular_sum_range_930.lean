-- Prove2me | solution 1 for FiniteTriangular.sum_range_930
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:55:32.51522+00:00
-- url     : https://prove2.me/submissions/80f70c43-8793-41de-9b9f-e106ed0b3e44

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 930, k = 431985 := by
  rw [sum_range_id]
