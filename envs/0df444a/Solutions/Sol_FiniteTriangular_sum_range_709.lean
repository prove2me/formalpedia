-- Prove2me | solution 1 for FiniteTriangular.sum_range_709
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:06:58.876893+00:00
-- url     : https://prove2.me/submissions/1b1f268d-2bca-4528-b912-2852605bbfc5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 709, k = 250986 := by
  rw [sum_range_id]
