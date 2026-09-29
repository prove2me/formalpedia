-- Prove2me | solution 1 for FiniteTriangular.sum_range_856
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:38:36.358441+00:00
-- url     : https://prove2.me/submissions/b6a362fe-063c-47b2-bc15-18ee6573b577

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 856, k = 365940 := by
  rw [sum_range_id]
