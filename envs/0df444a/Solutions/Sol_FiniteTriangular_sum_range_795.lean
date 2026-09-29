-- Prove2me | solution 1 for FiniteTriangular.sum_range_795
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:26:44.40321+00:00
-- url     : https://prove2.me/submissions/285951c8-0935-4ec0-b940-40791d917957

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 795, k = 315615 := by
  rw [sum_range_id]
