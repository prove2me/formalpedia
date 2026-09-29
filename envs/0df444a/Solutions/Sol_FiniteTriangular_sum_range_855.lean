-- Prove2me | solution 1 for FiniteTriangular.sum_range_855
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:38:35.674598+00:00
-- url     : https://prove2.me/submissions/b7397974-51ef-407f-8004-4ee01b624a28

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 855, k = 365085 := by
  rw [sum_range_id]
