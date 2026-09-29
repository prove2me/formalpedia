-- Prove2me | solution 1 for FiniteTriangular.sum_range_223
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:53:29.000142+00:00
-- url     : https://prove2.me/submissions/63b6c65e-cb8b-4c4e-89d2-c606a495a394

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 223, k = 24753 := by
  rw [sum_range_id]
