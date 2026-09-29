-- Prove2me | solution 1 for FiniteTriangular.sum_range_702
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:05:12.674658+00:00
-- url     : https://prove2.me/submissions/33cad043-1c68-4020-ba79-c3702118348f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 702, k = 246051 := by
  rw [sum_range_id]
