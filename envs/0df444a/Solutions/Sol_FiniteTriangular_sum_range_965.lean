-- Prove2me | solution 1 for FiniteTriangular.sum_range_965
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T12:02:48.33543+00:00
-- url     : https://prove2.me/submissions/d8812426-4fea-4fb3-bd8e-53c102c0fff0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 965, k = 465130 := by
  rw [sum_range_id]
