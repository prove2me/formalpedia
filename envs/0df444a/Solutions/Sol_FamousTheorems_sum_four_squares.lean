-- Prove2me | solution 1 for FamousTheorems.sum_four_squares
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:36.963895+00:00
-- url     : https://prove2.me/submissions/a5c66d93-9a17-40a9-9f0c-ac4746d5713e

import Mathlib

theorem solution : ∀ n : ℕ, ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n :=
  Nat.sum_four_squares
