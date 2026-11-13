-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB176_bounded_occupation_density_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:40:17.631215+00:00
-- url     : https://prove2.me/submissions/e34d24fe-853f-4f85-b444-105d16a8eaf3

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    (ℓ : ℝ → ℝ≥0∞) (B : ℝ≥0∞) (a b : ℝ)
    (hℓ : ∀ z, ℓ z ≤ B) :
    ∫⁻ z in Ioo a b, ℓ z ∂volume ≤
      B * volume (Ioo a b) := by
  calc
    ∫⁻ z in Ioo a b, ℓ z ∂volume ≤
        ∫⁻ z in Ioo a b, B ∂volume := by
      exact lintegral_mono hℓ
    _ = B * volume (Ioo a b) := by
      simp [mul_comm]
