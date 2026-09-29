-- Prove2me | solution 1 for FiniteTriangular.sum_range_514
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:24:05.547777+00:00
-- url     : https://prove2.me/submissions/cde9e632-89f3-4f04-bb68-3d52d9527bf8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 514, k = 131841 := by
  rw [sum_range_id]
