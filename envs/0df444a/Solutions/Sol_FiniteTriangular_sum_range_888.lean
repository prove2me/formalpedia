-- Prove2me | solution 1 for FiniteTriangular.sum_range_888
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:45:21.544988+00:00
-- url     : https://prove2.me/submissions/1f4d9372-7771-49d7-8d0c-d71cc3c642c9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 888, k = 393828 := by
  rw [sum_range_id]
