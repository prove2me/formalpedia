-- Prove2me | solution 1 for FamousTheorems.three_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:58.981322+00:00
-- url     : https://prove2.me/submissions/5f88ac08-5d42-44de-adfd-9657b46246af

import Mathlib

theorem solution : ∀ n : ℕ, 3 ∣ n ↔ 3 ∣ (Nat.digits 10 n).sum :=
  Nat.three_dvd_iff
