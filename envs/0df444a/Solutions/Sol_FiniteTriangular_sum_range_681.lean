-- Prove2me | solution 1 for FiniteTriangular.sum_range_681
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:01:59.495322+00:00
-- url     : https://prove2.me/submissions/2c4af359-42ea-4e7e-9cc0-b758dedf33af

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 681, k = 231540 := by
  rw [sum_range_id]
