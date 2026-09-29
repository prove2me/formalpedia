-- Prove2me | solution 1 for FiniteTriangular.sum_range_806
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:28:30.058115+00:00
-- url     : https://prove2.me/submissions/116449ae-fbef-4e01-be84-44056afd3413

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 806, k = 324415 := by
  rw [sum_range_id]
