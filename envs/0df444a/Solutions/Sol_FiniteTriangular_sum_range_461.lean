-- Prove2me | solution 1 for FiniteTriangular.sum_range_461
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:12:04.762877+00:00
-- url     : https://prove2.me/submissions/585fce7a-b06b-4ae4-8e9e-e0986cd01a5e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 461, k = 106030 := by
  rw [sum_range_id]
