-- Prove2me | solution 1 for FiniteTriangular.sum_range_852
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:38:33.008426+00:00
-- url     : https://prove2.me/submissions/60563400-e5b2-48d8-ab42-d7b71348b1dc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 852, k = 362526 := by
  rw [sum_range_id]
