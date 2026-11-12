-- Prove2me | solution 2 for AvramDividend.Classical.avram_gledger101_original_strict_clipped_clock_payment_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:48:43.2342+00:00
-- url     : https://prove2.me/submissions/d427aba0-96a4-4f2f-b812-2801cd3097f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Strictly interior stopped-clock payment times precede ruin on the original clock. -/
theorem solution
    (σ : ℝ≥0∞) (ρ : ℝ≥0) (hρ : (ρ : ℝ≥0∞) ≤ σ) :
    Ioo (0 : ℝ) (ρ : ℝ) ⊆ paymentTimes σ ∩ Iio (ρ : ℝ) := by
  intro t ht
  have ht0 : 0 < t := ht.1
  have htReal : (t.toNNReal : ℝ) = t := by
    exact Real.coe_toNNReal t (le_of_lt ht0)
  have htNN : t.toNNReal < ρ := by
    exact_mod_cast (show (t.toNNReal : ℝ) < (ρ : ℝ) from by
      rw [htReal]
      exact ht.2)
  have htENN : (t.toNNReal : ℝ≥0∞) < σ :=
    lt_of_lt_of_le (by exact_mod_cast htNN) hρ
  have htPay : t ∈ paymentTimes σ := by
    change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ)
    exact ⟨le_of_lt ht0, Or.inr (by
      change (t.toNNReal : ℝ≥0∞) < σ
      exact htENN)⟩
  exact ⟨htPay, ht.2⟩
