-- Prove2me | solution 1 for FiniteTriangular.sum_range_640
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:51:53.473552+00:00
-- url     : https://prove2.me/submissions/33b9b1fb-fb98-443e-a58c-acb1814611ab

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 640, k = 204480 := by
  rw [sum_range_id]
