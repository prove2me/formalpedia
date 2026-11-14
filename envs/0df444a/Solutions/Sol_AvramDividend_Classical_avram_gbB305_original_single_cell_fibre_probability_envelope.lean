-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB305_original_single_cell_fibre_probability_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:38:52.850599+00:00
-- url     : https://prove2.me/submissions/58ef683b-d9eb-48cf-afbd-bdaf777e8f9d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB294b_probability_fibre_integral_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- An original probability-time event confined to one cell inherits the integrated source-fibre bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (a b : ℝ) (g : ℝ → ℝ≥0∞) (C : ℝ≥0∞)
    (hInside : ∀ t ∈ Set.Ioo a b,
      P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t)
    (hOutside : ∀ t ∉ Set.Ioo a b,
      P ((fun ω : Ω => (ω, t)) ⁻¹' S) = 0)
    (hIntegral : (∫⁻ t in Set.Ioo a b, g t ∂volume) ≤ C) :
    (P.prod volume) S ≤ C := by
  let F : ℝ → ℝ≥0∞ := (Set.Ioo a b).indicator g
  have hPoint (t : ℝ) :
      P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ F t := by
    by_cases ht : t ∈ Set.Ioo a b
    · simpa only [F, Set.indicator_of_mem ht] using hInside t ht
    · simp only [F, Set.indicator_of_notMem ht, hOutside t ht, le_refl]
  have hBound :=
    avram_gbB294b_probability_fibre_integral_envelope
      P S hS F hPoint
  calc
    (P.prod volume) S ≤ (∫⁻ t : ℝ, F t ∂volume) := hBound
    _ = ∫⁻ t in Set.Ioo a b, g t ∂volume := by
      simp only [F, lintegral_indicator measurableSet_Ioo]
    _ ≤ C := hIntegral
