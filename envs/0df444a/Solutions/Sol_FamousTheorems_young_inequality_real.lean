-- Prove2me | solution 1 for FamousTheorems.young_inequality_real
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:03:51.803818+00:00
-- url     : https://prove2.me/submissions/1547d217-7c2a-4a20-8065-9532ad5e5ef4

import Mathlib

theorem solution (a b : ℝ) {p q : ℝ} (hpq : p.HolderConjugate q) :
    a * b ≤ |a| ^ p / p + |b| ^ q / q :=
  Real.young_inequality a b hpq
