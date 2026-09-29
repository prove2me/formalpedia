-- Prove2me | solution 1 for FamousTheorems.fermat_last_theorem_three
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:02:25.822506+00:00
-- url     : https://prove2.me/submissions/de4fbba9-0f1b-4d90-b89a-11ef153ea869

import Mathlib

theorem solution : ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ^ 3 + b ^ 3 ≠ c ^ 3 :=
  fermatLastTheoremThree
