-- Prove2me | solution 1 for FiniteTriangular.sum_range_799
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:26:46.988502+00:00
-- url     : https://prove2.me/submissions/31c4e376-5999-4274-ab2c-ee860d66ff8f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 799, k = 318801 := by
  rw [sum_range_id]
