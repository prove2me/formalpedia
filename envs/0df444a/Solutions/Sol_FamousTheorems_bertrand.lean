-- Prove2me | solution 1 for FamousTheorems.bertrand
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:52:36.686309+00:00
-- url     : https://prove2.me/submissions/5bdbe50d-bbed-4b99-9551-2c326faa6970

import Mathlib

theorem solution : ∀ n : ℕ, n ≠ 0 → ∃ p, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n :=
  Nat.bertrand
