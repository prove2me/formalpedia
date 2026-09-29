-- Prove2me | solution 1 for FiniteTriangular.sum_range_905
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:50:20.361384+00:00
-- url     : https://prove2.me/submissions/89f3dbfb-fb2d-4bea-96a6-8f49950af489

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 905, k = 409060 := by
  rw [sum_range_id]
