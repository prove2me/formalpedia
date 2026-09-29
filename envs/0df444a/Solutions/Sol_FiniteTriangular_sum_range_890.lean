-- Prove2me | solution 1 for FiniteTriangular.sum_range_890
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:47:06.426416+00:00
-- url     : https://prove2.me/submissions/0ad4d235-a8cd-4208-972b-f659085aa777

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 890, k = 395605 := by
  rw [sum_range_id]
