-- Prove2me | solution 1 for FiniteTriangular.sum_range_877
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:43:43.194401+00:00
-- url     : https://prove2.me/submissions/be10a4f4-a637-47c1-8361-1d1fd415c60a

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 877, k = 384126 := by
  rw [sum_range_id]
