-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:17:24.333069+00:00
-- url     : https://prove2.me/submissions/49e46986-9f05-4776-bb55-94944a83146b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Centred Brownian short tube implies genuine original source short tube. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSource : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ)) :
    ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |X.X s ω| ≤ (1 / 400 : ℝ) := by
  intro s hs
  rw [hSource s hs]
  have hB := hCentered s hs
  have hS0 : 0 ≤ (s : ℝ) := s.property
  have hShi : (s : ℝ) ≤ (1 / 1000 : ℝ) := hs
  have hDrift : 0 ≤ 2 * (s : ℝ) :=
    mul_nonneg (by norm_num) hS0
  have hTri := abs_add_le (B s) (2 * (s : ℝ))
  rw [abs_of_nonneg hDrift] at hTri
  linarith
