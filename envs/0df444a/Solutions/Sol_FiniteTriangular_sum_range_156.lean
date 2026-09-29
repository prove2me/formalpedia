-- Prove2me | solution 1 for FiniteTriangular.sum_range_156
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:19:11.797275+00:00
-- url     : https://prove2.me/submissions/51c3cfd5-2b56-4826-9d3c-3e43fa7cc427

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 156, k = 12090 := by
  rw [sum_range_id]
