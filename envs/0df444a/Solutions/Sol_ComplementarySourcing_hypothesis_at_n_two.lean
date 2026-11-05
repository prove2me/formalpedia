-- Prove2me | solution 1 for ComplementarySourcing.hypothesis_at_n_two
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T15:08:28.417004+00:00
-- url     : https://prove2.me/submissions/404a003c-6327-4003-a091-eb06511dd83d

import Mathlib

set_option linter.unusedVariables false

theorem solution {ε₀ σ : ℝ} (hε₀ : 0 < ε₀) (hσ₀ : 0 ≤ σ)
    (hσ : σ / ε₀ ≤ 3 - 2 * Real.sqrt 2) :
    0 < ε₀ - σ ∧
      (ε₀ + σ) ^ 2 / (2 * (ε₀ - σ)) ≤ ε₀ - σ ∧
      (ε₀ - 1 / 2 * (ε₀ + σ)) / (1 / 2) = ε₀ - σ ∧
      2 * (ε₀ + σ) +
          max ((ε₀ - 1 / 2 * (ε₀ + σ)) / (1 / 2)) ((ε₀ + σ) ^ 2 / (2 * (ε₀ - σ))) =
        3 * ε₀ + σ := by
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hc : 3 - 2 * Real.sqrt 2 < 1 := by
    nlinarith [Real.sqrt_nonneg 2, hsqrt]
  have hr : σ ≤ (3 - 2 * Real.sqrt 2) * ε₀ := by
    have := (div_le_iff₀ hε₀).mp hσ
    nlinarith
  have hpos : 0 < ε₀ - σ := by nlinarith
  have hA : σ - (3 - 2 * Real.sqrt 2) * ε₀ ≤ 0 := by nlinarith
  have hB : σ - (3 + 2 * Real.sqrt 2) * ε₀ ≤ 0 := by
    nlinarith [Real.sqrt_nonneg 2]
  have hprod : 0 ≤ (σ - (3 - 2 * Real.sqrt 2) * ε₀) *
      (σ - (3 + 2 * Real.sqrt 2) * ε₀) :=
    mul_nonneg_of_nonpos_of_nonpos hA hB
  have hprod' : 0 ≤ σ ^ 2 - 6 * ε₀ * σ + ε₀ ^ 2 := by
    calc
      0 ≤ (σ - (3 - 2 * Real.sqrt 2) * ε₀) *
          (σ - (3 + 2 * Real.sqrt 2) * ε₀) := hprod
      _ = σ ^ 2 - 6 * ε₀ * σ + ε₀ ^ 2 := by
        ring_nf
        rw [hsqrt]
        ring
  have hquad : (ε₀ + σ) ^ 2 ≤ 2 * (ε₀ - σ) ^ 2 := by
    nlinarith [hprod']
  have h2 : (ε₀ + σ) ^ 2 / (2 * (ε₀ - σ)) ≤ ε₀ - σ := by
    rw [div_le_iff₀ (by positivity : 0 < 2 * (ε₀ - σ))]
    nlinarith
  have h3 : (ε₀ - 1 / 2 * (ε₀ + σ)) / (1 / 2) = ε₀ - σ := by ring
  have hmax : max ((ε₀ - 1 / 2 * (ε₀ + σ)) / (1 / 2))
      ((ε₀ + σ) ^ 2 / (2 * (ε₀ - σ))) = ε₀ - σ := by
    calc
      max ((ε₀ - 1 / 2 * (ε₀ + σ)) / (1 / 2))
          ((ε₀ + σ) ^ 2 / (2 * (ε₀ - σ))) =
          (ε₀ - 1 / 2 * (ε₀ + σ)) / (1 / 2) :=
        max_eq_left (by rw [h3]; exact h2)
      _ = ε₀ - σ := h3
  exact ⟨hpos, h2, h3, by rw [hmax]; ring⟩
