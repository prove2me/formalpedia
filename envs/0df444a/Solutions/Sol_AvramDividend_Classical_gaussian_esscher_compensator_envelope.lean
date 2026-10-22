-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_compensator_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:38:17.712187+00:00
-- url     : https://prove2.me/submissions/cc9de529-b93c-4d0c-bb8d-e4e0ba44de57

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_gaussian_compensated_jump_pos_linear
import Theorems.Thm_AvramDividend_Classical_gaussian_compensated_jump_quadratic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- The tilted Gaussian compensator is dominated by a Lévy-integrable quadratic/linear weight. -/
theorem solution
    (φ θ z : ℝ) (hφ : 0 < φ) (hθ : 0 ≤ θ) (hz : 0 ≤ z) :
    Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) ≤
      (θ + θ ^ 2) * (Real.exp (-φ * z) * min (z ^ 2) z) := by
  have hlin := (gaussian_compensated_jump_pos_linear θ z hθ hz).2
  have hquad := gaussian_compensated_jump_quadratic θ z hθ hz
  have hminor :
      Real.exp (-θ * z) - 1 + θ * z ≤
        (θ + θ ^ 2) * min (z ^ 2) z := by
    by_cases hsmall : z ≤ 1
    · have hs : z ^ 2 ≤ z := by nlinarith
      rw [min_eq_left hs]
      calc
        Real.exp (-θ * z) - 1 + θ * z ≤ (θ * z) ^ 2 := hquad
        _ = θ ^ 2 * z ^ 2 := by ring
        _ ≤ (θ + θ ^ 2) * z ^ 2 :=
          mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg θ]) (sq_nonneg z)
    · have hlarge : 1 ≤ z := le_of_lt (lt_of_not_ge hsmall)
      have hl : z ≤ z ^ 2 := by nlinarith
      rw [min_eq_right hl]
      calc
        Real.exp (-θ * z) - 1 + θ * z ≤ θ * z := hlin
        _ ≤ (θ + θ ^ 2) * z :=
          mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg θ]) hz
  calc
    Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) ≤
        Real.exp (-φ * z) * ((θ + θ ^ 2) * min (z ^ 2) z) :=
      mul_le_mul_of_nonneg_left hminor (le_of_lt (Real.exp_pos _))
    _ = (θ + θ ^ 2) * (Real.exp (-φ * z) * min (z ^ 2) z) := by ring
