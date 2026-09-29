-- Prove2me | solution 1 for FiniteTriangular.sum_range_613
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:46:44.053556+00:00
-- url     : https://prove2.me/submissions/01cce19b-3bd7-46e9-ac6f-89718e528495

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 613, k = 187578 := by
  rw [sum_range_id]
