-- Prove2me | solution 1 for FiniteTriangular.sum_range_175
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:22:18.709292+00:00
-- url     : https://prove2.me/submissions/d55ad21f-e5c2-42ec-8c78-772c25226b4f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 175, k = 15225 := by
  rw [sum_range_id]
