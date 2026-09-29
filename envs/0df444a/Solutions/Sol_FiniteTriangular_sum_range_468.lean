-- Prove2me | solution 1 for FiniteTriangular.sum_range_468
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:13:50.874755+00:00
-- url     : https://prove2.me/submissions/a80a5240-fda1-4ade-a46b-f7bd1aed94d8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 468, k = 109278 := by
  rw [sum_range_id]
