-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump12_original_initial_event_masked_jump_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T18:21:59.399488+00:00
-- url     : https://prove2.me/submissions/e3c92682-43c1-4e68-8c71-e7e0804a6760

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_measure_zero_initial_time

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- Initial-event masking commutes with the original stopped negative-jump
integral because the source jump measure assigns no mass to time zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (σ : Ω → ℝ≥0)
    (H : Ω → (ℝ≥0 × ℝ) → ℝ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    ∀ ω,
      (∫ p, (if p.1 ≤ A.indicator σ ω then H ω p else 0) ∂(NX ω)) =
        A.indicator (fun ξ =>
          ∫ p, (if p.1 ≤ σ ξ then H ξ p else 0) ∂(NX ξ)) ω := by
  intro NX ω
  by_cases hA : ω ∈ A
  · simp [Set.indicator, hA]
  · have hRect :
        NX ω ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set ℝ)) = 0 := by
      simpa only [NX] using
        (avram_wave5_01_actual_source_jump_measure_zero_initial_time
          X ω Set.univ MeasurableSet.univ)
    have hSet :
        {p : ℝ≥0 × ℝ | p.1 ≤ (0 : ℝ≥0)} =
          ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set ℝ)) := by
      ext p
      simp [le_zero_iff]
    have hNull : NX ω {p : ℝ≥0 × ℝ | p.1 ≤ (0 : ℝ≥0)} = 0 := by
      simpa only [hSet] using hRect
    have hAE : ∀ᵐ p ∂(NX ω), ¬ p.1 ≤ (0 : ℝ≥0) := by
      apply (ae_iff).2
      simpa only [not_not] using hNull
    have hZero :
        (∫ p, (if p.1 ≤ (0 : ℝ≥0) then H ω p else 0) ∂(NX ω)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hAE] with p hp
      simp [hp]
    simpa [Set.indicator, hA] using hZero
