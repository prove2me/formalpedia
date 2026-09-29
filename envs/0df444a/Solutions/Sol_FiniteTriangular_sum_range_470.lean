-- Prove2me | solution 1 for FiniteTriangular.sum_range_470
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:13:52.154908+00:00
-- url     : https://prove2.me/submissions/9a512526-c273-4ba6-a73b-2f8611bc7545

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 470, k = 110215 := by
  rw [sum_range_id]
