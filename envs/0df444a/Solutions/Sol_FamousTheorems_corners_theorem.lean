-- Prove2me | solution 1 for FamousTheorems.corners_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:19:53.084257+00:00
-- url     : https://prove2.me/submissions/b1d28550-b78e-43fe-8d4d-fd1d985ac14a

import Mathlib

theorem solution {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hn : cornersTheoremBound (ε / 9) ≤ n) (A : Finset (ℕ × ℕ))
    (hAn : A ⊆ Finset.range n ×ˢ Finset.range n) (hAε : ε * n ^ 2 ≤ A.card) :
    ¬ IsCornerFree (A : Set (ℕ × ℕ)) :=
  corners_theorem_nat hε hn A hAn hAε
