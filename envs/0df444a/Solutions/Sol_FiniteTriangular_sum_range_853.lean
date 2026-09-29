-- Prove2me | solution 1 for FiniteTriangular.sum_range_853
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:38:33.651638+00:00
-- url     : https://prove2.me/submissions/63c98fc1-ec7b-4db4-a7e0-f2ee4d795175

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 853, k = 363378 := by
  rw [sum_range_id]
