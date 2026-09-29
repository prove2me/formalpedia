-- Prove2me | solution 1 for FiniteTriangular.sum_range_322
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:32:34.966187+00:00
-- url     : https://prove2.me/submissions/8f4588a4-fe8d-4716-950f-24fa62fdb687

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 322, k = 51681 := by
  rw [sum_range_id]
