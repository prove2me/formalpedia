-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:27:10.175864+00:00
-- url     : https://prove2.me/submissions/c61f59f9-f25e-410e-9473-461f2e35240a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
    Measurable[𝓕.rightCont.predictable] a ∧
    (∀ p, |a p| ≤ (1 : ℝ)) ∧
    (∀ p, T < p.1 → a p = 0) := by
  classical
  intro a
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hDisc :=
    avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
      (𝓕 := 𝓕) q hq T
  have hSurvM : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω =>
        if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0) := by
    exact (avram_wave3_04_inclusiveSurvival_stronglyPredictable τ hτ).measurable
  refine ⟨?_, ?_, ?_⟩
  · exact hDisc.1.mul hSurvM
  · intro p
    by_cases hp : (p.1 : ℝ≥0∞) ≤ τ p.2
    · simpa [a, hp] using hDisc.2.1 p
    · simp [a, hp]
  · intro p hp
    simp [a, not_le.mpr hp]
