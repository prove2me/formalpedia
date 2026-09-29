-- Prove2me | solution 1 for FiniteTriangular.sum_range_742
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:14:45.086489+00:00
-- url     : https://prove2.me/submissions/093c4c05-0809-4e13-b810-898249c175f8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 742, k = 274911 := by
  rw [sum_range_id]
