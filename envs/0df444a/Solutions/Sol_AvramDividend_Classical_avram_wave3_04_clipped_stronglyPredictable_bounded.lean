-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_clipped_stronglyPredictable_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:41:33.906635+00:00
-- url     : https://prove2.me/submissions/d7f0592e-dc94-4cdd-938f-a6625bc6ac53

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal

/-- Symmetric clipping of a strongly predictable real process remains
strongly predictable, with a deterministic pointwise norm bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕 Z)
    (K : ℝ) (hK : 0 ≤ K) :
    IsStronglyPredictable 𝓕
      (fun t ω => max (-K) (min K (Z t ω))) ∧
    (∀ t ω, ‖max (-K) (min K (Z t ω))‖ ≤ K) := by
  constructor
  · change StronglyMeasurable[𝓕.predictable]
      (fun p : ℝ≥0 × Ω => max (-K) (min K (Z p.1 p.2)))
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
    have hclamp : Measurable (fun z : ℝ => max (-K) (min K z)) := by
      fun_prop
    exact (hclamp.comp hZ.measurable).stronglyMeasurable
  · intro t ω
    have hlo : -K ≤ max (-K) (min K (Z t ω)) :=
      le_max_left _ _
    have hup : max (-K) (min K (Z t ω)) ≤ K := by
      exact max_le (by linarith) (min_le_left _ _)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, hup⟩
