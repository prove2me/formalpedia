-- Prove2me | solution 1 for FiniteTriangular.sum_range_303
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:20:08.146914+00:00
-- url     : https://prove2.me/submissions/c26d9ba8-ccd7-49e0-b101-5ac6bf1287ed

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 303, k = 45753 := by
  rw [sum_range_id]
