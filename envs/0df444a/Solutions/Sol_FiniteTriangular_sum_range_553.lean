-- Prove2me | solution 1 for FiniteTriangular.sum_range_553
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:34:24.545433+00:00
-- url     : https://prove2.me/submissions/d30b319e-7e77-473a-a995-dd3b5ad63326

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 553, k = 152628 := by
  rw [sum_range_id]
