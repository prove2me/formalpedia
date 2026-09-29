-- Prove2me | solution 1 for FiniteTriangular.sum_range_555
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:34:25.807294+00:00
-- url     : https://prove2.me/submissions/baac7a9a-6bbb-4442-ba55-b1935e675365

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 555, k = 153735 := by
  rw [sum_range_id]
