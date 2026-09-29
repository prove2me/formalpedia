-- Prove2me | solution 1 for FiniteTriangular.sum_range_359
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:39:30.135815+00:00
-- url     : https://prove2.me/submissions/1cb75981-ed2b-4cda-abdf-388ddefd3720

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 359, k = 64261 := by
  rw [sum_range_id]
