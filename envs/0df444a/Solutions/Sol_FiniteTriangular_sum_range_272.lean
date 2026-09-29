-- Prove2me | solution 1 for FiniteTriangular.sum_range_272
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:13:02.96585+00:00
-- url     : https://prove2.me/submissions/16bbc615-54b8-45f9-966d-9fe0d287fd3e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 272, k = 36856 := by
  rw [sum_range_id]
