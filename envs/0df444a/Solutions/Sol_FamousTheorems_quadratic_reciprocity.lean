-- Prove2me | solution 1 for FamousTheorems.quadratic_reciprocity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:17:24.78299+00:00
-- url     : https://prove2.me/submissions/ba07a841-2f54-4a8f-b1c1-ce5649d7eced

import Mathlib

theorem solution : ∀ {p q : ℕ} [Fact (Nat.Prime p)] [Fact (Nat.Prime q)], p ≠ 2 → q ≠ 2 → p ≠ q →
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) :=
  legendreSym.quadratic_reciprocity
