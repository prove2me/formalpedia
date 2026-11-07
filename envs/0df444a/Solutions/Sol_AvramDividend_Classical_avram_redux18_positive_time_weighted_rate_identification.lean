-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux18_positive_time_weighted_rate_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:21:47.104649+00:00
-- url     : https://prove2.me/submissions/bfdf7fe7-e08a-4304-aeb0-6418354f4653

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-! Cancel positive finite time from negative-band count rates, then integrate. -/
theorem solution
    (t : ℝ≥0∞) (ht0 : t ≠ 0) (htTop : t ≠ ⊤)
    (μ ν : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hCounts : ∀ C : Set ℝ, MeasurableSet C → C ⊆ B →
      t * μ C = t * ν C) (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in B, g y ∂μ) = (∫⁻ y in B, g y ∂ν) := by
  have hres : μ.restrict B = ν.restrict B := by
    ext C hC
    rw [Measure.restrict_apply hC, Measure.restrict_apply hC]
    have hScaled : μ (C ∩ B) * t = ν (C ∩ B) * t := by
      calc
        μ (C ∩ B) * t = t * μ (C ∩ B) := mul_comm _ _
        _ = t * ν (C ∩ B) :=
          hCounts (C ∩ B) (hC.inter hB) inter_subset_right
        _ = ν (C ∩ B) * t := mul_comm _ _
    exact (ENNReal.mul_left_inj ht0 htTop).mp hScaled
  change (∫⁻ y, g y ∂μ.restrict B) =
    (∫⁻ y, g y ∂ν.restrict B)
  rw [hres]
