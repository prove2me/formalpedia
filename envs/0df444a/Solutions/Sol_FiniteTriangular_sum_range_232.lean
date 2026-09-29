-- Prove2me | solution 1 for FiniteTriangular.sum_range_232
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:55:16.081809+00:00
-- url     : https://prove2.me/submissions/65ac6b18-9770-4034-b9e0-70f2f31ab37a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 232, k = 26796 := by
  rw [sum_range_id]
