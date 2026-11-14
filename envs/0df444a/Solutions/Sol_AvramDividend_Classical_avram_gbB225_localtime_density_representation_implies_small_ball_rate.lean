-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB225_localtime_density_representation_implies_small_ball_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:07:21.467227+00:00
-- url     : https://prove2.me/submissions/7390c676-8706-4462-845a-966676db2e04

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB176_bounded_occupation_density_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_gbB177_real_symmetric_interval_volume
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- Bounded spatial occupation density bounds each shrinking stopped time band. -/
theorem solution
    (f : ℝ → ℝ) (n : ℕ) (ρ y : ℝ)
    (ℓ : ℝ → ℝ≥0∞) (B : ℝ≥0∞)
    (hℓ : ∀ z, ℓ z ≤ B)
    (hOccupation : ∀ ε : ℝ, 0 < ε →
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
        |f t - y| < ε} =
      ∫⁻ z in Set.Ioo (y - ε) (y + ε), ℓ z ∂volume) :
    ∀ k : ℕ,
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
        |f t - y| < (1 : ℝ) / ((k : ℝ) + 1)} ≤
      B * ENNReal.ofReal (2 * ((1 : ℝ) / ((k : ℝ) + 1))) := by
  intro k
  let ε : ℝ := (1 : ℝ) / ((k : ℝ) + 1)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  change volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ |f t - y| < ε} ≤
    B * ENNReal.ofReal (2 * ε)
  calc
    volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ |f t - y| < ε}
        = ∫⁻ z in Set.Ioo (y - ε) (y + ε), ℓ z ∂volume :=
          hOccupation ε hε
    _ ≤ B * volume (Set.Ioo (y - ε) (y + ε)) :=
      avram_gbB176_bounded_occupation_density_lintegral
        ℓ B (y - ε) (y + ε) hℓ
    _ = B * ENNReal.ofReal (2 * ε) := by
      rw [avram_gbB177_real_symmetric_interval_volume]

