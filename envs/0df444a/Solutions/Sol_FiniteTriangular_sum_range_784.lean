-- Prove2me | solution 1 for FiniteTriangular.sum_range_784
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:23:26.126252+00:00
-- url     : https://prove2.me/submissions/0070089b-6540-4277-8137-aa3a70a45c7f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 784, k = 306936 := by
  rw [sum_range_id]
