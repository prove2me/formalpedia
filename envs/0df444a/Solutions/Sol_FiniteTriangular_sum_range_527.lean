-- Prove2me | solution 1 for FiniteTriangular.sum_range_527
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:25:54.474438+00:00
-- url     : https://prove2.me/submissions/306a2b26-191e-4c02-8377-2974bc4a47f9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 527, k = 138601 := by
  rw [sum_range_id]
