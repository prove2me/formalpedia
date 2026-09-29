-- Prove2me | solution 1 for FiniteTriangular.sum_range_733
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:12:46.213179+00:00
-- url     : https://prove2.me/submissions/1f159585-4925-447b-8186-3d4b09e1069c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 733, k = 268278 := by
  rw [sum_range_id]
