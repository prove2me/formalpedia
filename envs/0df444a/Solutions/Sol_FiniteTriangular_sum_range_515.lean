-- Prove2me | solution 1 for FiniteTriangular.sum_range_515
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:24:06.233638+00:00
-- url     : https://prove2.me/submissions/48e31290-73cd-40da-b9c2-53014d07e4f0

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 515, k = 132355 := by
  rw [sum_range_id]
