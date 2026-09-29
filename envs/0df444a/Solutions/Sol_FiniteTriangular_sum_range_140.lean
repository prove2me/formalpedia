-- Prove2me | solution 1 for FiniteTriangular.sum_range_140
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:16:18.180653+00:00
-- url     : https://prove2.me/submissions/a8b0f4fb-e2ad-4daa-b5e0-eb4767310edd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 140, k = 9730 := by
  rw [sum_range_id]
