-- Prove2me | solution 1 for FiniteTriangular.sum_range_1011
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:42:28.09665+00:00
-- url     : https://prove2.me/submissions/20d86048-9338-43bf-a9aa-dc9e3d25c821

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1011, k = 510555 := by
  rw [sum_range_id]
