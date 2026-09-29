-- Prove2me | solution 1 for FiniteTriangular.sum_range_486
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:17:23.613144+00:00
-- url     : https://prove2.me/submissions/a3b84f04-a35d-4ea5-9e59-526720845ecf

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 486, k = 117855 := by
  rw [sum_range_id]
