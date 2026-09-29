-- Prove2me | solution 1 for FiniteTriangular.sum_range_674
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:00:09.644502+00:00
-- url     : https://prove2.me/submissions/7dec16ec-96f7-493b-a780-398da31989ec

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 674, k = 226801 := by
  rw [sum_range_id]
