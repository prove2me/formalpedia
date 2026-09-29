-- Prove2me | solution 1 for FiniteTriangular.sum_range_739
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:14:43.296473+00:00
-- url     : https://prove2.me/submissions/dca2bfa1-4dda-4536-8c07-5461035ec2f3

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 739, k = 272691 := by
  rw [sum_range_id]
