-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger101_original_strict_clipped_clock_payment_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:48:01.785873+00:00
-- url     : https://prove2.me/submissions/8c26f1af-cf6f-4d3d-9209-3d317ea50106

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive times strictly before a clock bounded by ruin remain admissible
    payment times for the original ruin-time mask. -/
theorem solution
    (σ : ℝ≥0∞) (ρ : ℝ≥0) (hρ : (ρ : ℝ≥0∞) ≤ σ) :
    Ioo (0 : ℝ) (ρ : ℝ) ⊆ paymentTimes σ ∩ Iio (ρ : ℝ) := by
  intro t ht
  rcases ht with ⟨ht0, htρ⟩
  have htNN : (Real.toNNReal t) < ρ := by
    rw [Real.toNNReal_of_nonneg (le_of_lt ht0)]
    exact_mod_cast htρ
  have htCast : ENNReal.ofReal t < (ρ : ℝ≥0∞) := by
    change ((Real.toNNReal t : ℝ≥0) : ℝ≥0∞) < (ρ : ℝ≥0∞)
    exact_mod_cast htNN
  refine ⟨?_, htρ⟩
  change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < σ)
  exact ⟨le_of_lt ht0, Or.inr (lt_of_lt_of_le htCast hρ)⟩
