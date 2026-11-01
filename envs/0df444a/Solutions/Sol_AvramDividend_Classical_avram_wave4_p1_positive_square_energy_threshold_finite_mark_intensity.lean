-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_positive_square_energy_threshold_finite_mark_intensity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:25:53.885131+00:00
-- url     : https://prove2.me/submissions/2726c7b6-e1ad-4737-bd21-c56e29153126

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem solution
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    (g : E → ℝ≥0∞) (hg : Measurable g)
    (henergy : ∫⁻ z, g z ∂ν < ∞)
    (B : Set E) (hB : MeasurableSet B)
    (ε : ℝ≥0∞) (hε : 0 < ε)
    (hthreshold : ∀ z ∈ B, ε ≤ g z) :
    ν B < ∞ := by
  have hlow : ε * ν B ≤ ∫⁻ z in B, g z ∂ν := by
    calc
      ε * ν B = ∫⁻ z in B, ε ∂ν := by rw [setLIntegral_const]
      _ ≤ ∫⁻ z in B, g z ∂ν :=
        setLIntegral_mono hg hthreshold
  have hbound : ε * ν B < ∞ :=
    lt_of_le_of_lt (hlow.trans (setLIntegral_le_lintegral B g)) henergy
  exact ENNReal.lt_top_of_mul_ne_top_right hbound.ne (ne_of_gt hε)
