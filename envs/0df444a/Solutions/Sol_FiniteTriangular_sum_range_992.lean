-- Prove2me | solution 1 for FiniteTriangular.sum_range_992
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:37:08.30902+00:00
-- url     : https://prove2.me/submissions/8cc4f3d0-fc73-400a-a5c6-ab0123e441db

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 992, k = 491536 := by
  rw [sum_range_id]
