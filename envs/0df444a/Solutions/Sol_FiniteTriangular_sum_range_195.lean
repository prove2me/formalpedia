-- Prove2me | solution 1 for FiniteTriangular.sum_range_195
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:47:32.907171+00:00
-- url     : https://prove2.me/submissions/85415427-418f-4efa-8355-3488f8ad8440

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 195, k = 18915 := by
  rw [sum_range_id]
