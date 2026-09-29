-- Prove2me | solution 1 for FiniteTriangular.sum_range_444
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:08:14.940298+00:00
-- url     : https://prove2.me/submissions/514bce44-7841-4d54-8756-871636f018dd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 444, k = 98346 := by
  rw [sum_range_id]
