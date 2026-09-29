-- Prove2me | solution 1 for FiniteTriangular.sum_range_949
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:59:09.046376+00:00
-- url     : https://prove2.me/submissions/56959a22-1901-4dd4-b472-26951aa68d1e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 949, k = 449826 := by
  rw [sum_range_id]
