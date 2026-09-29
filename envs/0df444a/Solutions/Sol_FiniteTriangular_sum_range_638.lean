-- Prove2me | solution 1 for FiniteTriangular.sum_range_638
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:51:52.296109+00:00
-- url     : https://prove2.me/submissions/4f6c3ea6-6d10-438c-83e3-18dd1bc1b696

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 638, k = 203203 := by
  rw [sum_range_id]
