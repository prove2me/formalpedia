-- Prove2me | solution 1 for FiniteTriangular.sum_range_667
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:58:23.862484+00:00
-- url     : https://prove2.me/submissions/0268a377-647e-429f-ba71-90ddba64ea28

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 667, k = 222111 := by
  rw [sum_range_id]
