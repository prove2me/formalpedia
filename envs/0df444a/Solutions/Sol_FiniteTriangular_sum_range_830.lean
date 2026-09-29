-- Prove2me | solution 1 for FiniteTriangular.sum_range_830
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:33:44.40234+00:00
-- url     : https://prove2.me/submissions/fbfdc6a7-c56f-4ef5-baf4-a23f6692fc8e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 830, k = 344035 := by
  rw [sum_range_id]
