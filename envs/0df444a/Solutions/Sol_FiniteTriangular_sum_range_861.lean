-- Prove2me | solution 1 for FiniteTriangular.sum_range_861
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:40:12.095991+00:00
-- url     : https://prove2.me/submissions/5663dc77-b68b-48ab-bd6e-f6c20bc05bf1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 861, k = 370230 := by
  rw [sum_range_id]
