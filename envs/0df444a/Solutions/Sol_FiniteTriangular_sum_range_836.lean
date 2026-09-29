-- Prove2me | solution 1 for FiniteTriangular.sum_range_836
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:35:21.351333+00:00
-- url     : https://prove2.me/submissions/a6d43f87-f004-483e-bf3c-eebbeef8177f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 836, k = 349030 := by
  rw [sum_range_id]
