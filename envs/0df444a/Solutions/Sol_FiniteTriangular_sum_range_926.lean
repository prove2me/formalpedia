-- Prove2me | solution 1 for FiniteTriangular.sum_range_926
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:53:47.918752+00:00
-- url     : https://prove2.me/submissions/524d83ce-509c-4e52-9d72-9764bd319643

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 926, k = 428275 := by
  rw [sum_range_id]
