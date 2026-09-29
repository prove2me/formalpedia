-- Prove2me | solution 1 for FiniteTriangular.sum_range_804
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:28:32.455033+00:00
-- url     : https://prove2.me/submissions/1161c9e3-4659-469b-9ce4-beab4b7078d2

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 804, k = 322806 := by
  rw [sum_range_id]
