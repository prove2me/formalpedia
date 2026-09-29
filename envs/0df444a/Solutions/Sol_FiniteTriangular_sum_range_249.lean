-- Prove2me | solution 1 for FiniteTriangular.sum_range_249
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:09:12.680616+00:00
-- url     : https://prove2.me/submissions/0374fad8-ba9d-45af-b962-fb71214a08ae

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 249, k = 30876 := by
  rw [sum_range_id]
