-- Prove2me | solution 1 for FamousTheorems.sum_range_id
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:58.841337+00:00
-- url     : https://prove2.me/submissions/b685486b-492e-460a-b08b-2d02b0ebfe60

import Mathlib

theorem solution : ∀ n : ℕ, ∑ i ∈ Finset.range n, i = n * (n - 1) / 2 :=
  Finset.sum_range_id
