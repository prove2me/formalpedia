-- Prove2me | solution 1 for FiniteTriangular.sum_range_495
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:19:00.708797+00:00
-- url     : https://prove2.me/submissions/f96821c9-cd53-4132-9295-b210de21e011

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 495, k = 122265 := by
  rw [sum_range_id]
