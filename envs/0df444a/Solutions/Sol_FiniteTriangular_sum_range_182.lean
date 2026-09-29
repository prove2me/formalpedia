-- Prove2me | solution 1 for FiniteTriangular.sum_range_182
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:24:28.957772+00:00
-- url     : https://prove2.me/submissions/129873ba-0d08-46da-9457-26b64f6b2043

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 182, k = 16471 := by
  rw [sum_range_id]
