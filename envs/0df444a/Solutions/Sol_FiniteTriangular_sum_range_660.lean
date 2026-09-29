-- Prove2me | solution 1 for FiniteTriangular.sum_range_660
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:56:48.6945+00:00
-- url     : https://prove2.me/submissions/cfa16a68-f281-4cd6-acd9-49654f2746f9

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 660, k = 217470 := by
  rw [sum_range_id]
