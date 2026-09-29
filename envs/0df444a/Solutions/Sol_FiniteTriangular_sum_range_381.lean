-- Prove2me | solution 1 for FiniteTriangular.sum_range_381
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:45:22.641319+00:00
-- url     : https://prove2.me/submissions/c55ad4e9-2360-402b-a0ad-16238df21308

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 381, k = 72390 := by
  rw [sum_range_id]
