-- Prove2me | solution 1 for FiniteTriangular.sum_range_850
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:38:31.69312+00:00
-- url     : https://prove2.me/submissions/ff475969-089e-489e-8e09-b7d80ec3d849

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 850, k = 360825 := by
  rw [sum_range_id]
