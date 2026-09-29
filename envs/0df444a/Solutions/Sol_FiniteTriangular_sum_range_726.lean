-- Prove2me | solution 1 for FiniteTriangular.sum_range_726
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:11:00.485949+00:00
-- url     : https://prove2.me/submissions/8f8c5feb-13ae-47a3-b57c-e9ac81a57d39

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 726, k = 263175 := by
  rw [sum_range_id]
