-- Prove2me | solution 1 for FiniteTriangular.sum_range_604
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:44:55.158018+00:00
-- url     : https://prove2.me/submissions/fc4ae0fe-d322-486c-b262-66826860a243

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 604, k = 182106 := by
  rw [sum_range_id]
