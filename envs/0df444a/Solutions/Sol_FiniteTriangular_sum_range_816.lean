-- Prove2me | solution 1 for FiniteTriangular.sum_range_816
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:30:21.108224+00:00
-- url     : https://prove2.me/submissions/15b36e5f-7e98-4c4a-99fb-0111c16dc53f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 816, k = 332520 := by
  rw [sum_range_id]
