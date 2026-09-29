-- Prove2me | solution 1 for FiniteTriangular.sum_range_1018
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:44:08.908978+00:00
-- url     : https://prove2.me/submissions/77d72b55-5745-4659-83e4-6ba4029ac30e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1018, k = 517653 := by
  rw [sum_range_id]
