-- Prove2me | solution 1 for FamousTheorems.fermat_last_theorem_four
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:06:57.619652+00:00
-- url     : https://prove2.me/submissions/95bc0714-7eb6-431b-b2a6-60761c1acef8

import Mathlib

theorem solution : ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 4 + b ^ 4 ≠ c ^ 4 :=
  fermatLastTheoremFour
