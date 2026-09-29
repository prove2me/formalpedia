-- Prove2me | solution 1 for FiniteTriangular.sum_range_435
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:57:35.534888+00:00
-- url     : https://prove2.me/submissions/325f6195-67a7-4edc-9158-b3e2748b8707

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 435, k = 94395 := by
  rw [sum_range_id]
