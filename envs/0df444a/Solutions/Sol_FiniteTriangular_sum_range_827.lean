-- Prove2me | solution 1 for FiniteTriangular.sum_range_827
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:33:42.451302+00:00
-- url     : https://prove2.me/submissions/9520ea56-cab5-4410-b214-b54886092eff

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 827, k = 341551 := by
  rw [sum_range_id]
