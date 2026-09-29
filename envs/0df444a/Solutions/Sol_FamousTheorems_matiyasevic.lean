-- Prove2me | solution 1 for FamousTheorems.matiyasevic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:10:25.242924+00:00
-- url     : https://prove2.me/submissions/858ffb1f-3c9f-4f46-84ce-eb7b9af81c8d

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {a k x y : ℕ} :
    (∃ a1 : 1 < a, Pell.xn a1 k = x ∧ Pell.yn a1 k = y) ↔
      1 < a ∧ k ≤ y ∧ (x = 1 ∧ y = 0 ∨
        ∃ u v s t b : ℕ,
          x * x - (a * a - 1) * y * y = 1 ∧ u * u - (a * a - 1) * v * v = 1 ∧
          s * s - (b * b - 1) * t * t = 1 ∧ 1 < b ∧ b ≡ 1 [MOD 4 * y] ∧
          b ≡ a [MOD u] ∧ 0 < v ∧ y * y ∣ v ∧ s ≡ x [MOD u] ∧ t ≡ k [MOD 4 * y]) :=
  Pell.matiyasevic
