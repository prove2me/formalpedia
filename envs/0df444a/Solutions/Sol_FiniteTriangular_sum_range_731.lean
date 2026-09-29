-- Prove2me | solution 1 for FiniteTriangular.sum_range_731
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:12:44.836991+00:00
-- url     : https://prove2.me/submissions/97bf4abd-3c1e-47cb-9a85-81fc0026bbfa

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 731, k = 266815 := by
  rw [sum_range_id]
