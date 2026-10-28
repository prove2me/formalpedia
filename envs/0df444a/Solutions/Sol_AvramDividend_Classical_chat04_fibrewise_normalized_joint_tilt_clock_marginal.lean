-- Prove2me | solution 1 for AvramDividend.Classical.chat04_fibrewise_normalized_joint_tilt_clock_marginal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:44:37.492875+00:00
-- url     : https://prove2.me/submissions/fe3b867b-8e1e-4a4b-9592-a99db3b2be29

import Mathlib
open MeasureTheory Set
open scoped ENNReal
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (η : Measure ℝ) [IsProbabilityMeasure η]
    (D : Ω × ℝ → ℝ≥0∞) (hD : Measurable D)
    (hunit : ∀ t : ℝ, (∫⁻ ω, D (ω, t) ∂P) = 1) :
    Measure.map Prod.snd ((P.prod η).withDensity D) = η := by
  ext s hs
  have hm : MeasurableSet (Prod.snd ⁻¹' s : Set (Ω × ℝ)) := measurable_snd hs
  rw [Measure.map_apply measurable_snd hs, withDensity_apply _ hm, ← lintegral_indicator hm,
    lintegral_prod_symm _ ((hD.indicator hm).aemeasurable)]
  have : ∀ t : ℝ, (∫⁻ ω, (Prod.snd ⁻¹' s).indicator D (ω, t) ∂P) = s.indicator 1 t := by
    intro t
    by_cases ht : t ∈ s
    · simp [Set.indicator_of_mem, ht, hunit]
    · simp [ht]
  simp_rw [this]
  rw [lintegral_indicator hs]
  simp
