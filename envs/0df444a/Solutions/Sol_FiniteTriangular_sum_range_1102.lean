-- Prove2me | solution 1 for FiniteTriangular.sum_range_1102
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:25:43.598333+00:00
-- url     : https://prove2.me/submissions/68ec79ef-70f4-4ce9-bd84-37ac63c0afa1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1102, k = 606651 := by
  rw [sum_range_id]
