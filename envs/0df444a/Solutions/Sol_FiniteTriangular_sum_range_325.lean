-- Prove2me | solution 1 for FiniteTriangular.sum_range_325
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:32:32.621731+00:00
-- url     : https://prove2.me/submissions/d3506086-a333-484e-85e8-ce4050ee2745

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 325, k = 52650 := by
  rw [sum_range_id]
