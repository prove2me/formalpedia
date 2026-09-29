-- Prove2me | solution 1 for FiniteTriangular.sum_range_903
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:48:46.813459+00:00
-- url     : https://prove2.me/submissions/ed7581cb-8519-4705-8bf6-8879c7561099

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 903, k = 407253 := by
  rw [sum_range_id]
