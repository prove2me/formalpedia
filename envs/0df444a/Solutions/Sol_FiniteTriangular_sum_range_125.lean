-- Prove2me | solution 1 for FiniteTriangular.sum_range_125
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:13:22.76777+00:00
-- url     : https://prove2.me/submissions/3cb9e8bd-90c6-49a3-8677-f46e4a5bc2b2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 125, k = 7750 := by
  rw [sum_range_id]
