-- Prove2me | solution 1 for FiniteTriangular.sum_range_720
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:08:55.195223+00:00
-- url     : https://prove2.me/submissions/3a7d1bcc-efa8-412f-9ff7-a9d2855ce780

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 720, k = 258840 := by
  rw [sum_range_id]
