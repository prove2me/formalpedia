-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_rightcont_stopping_mask_of_stronglyMeasurable_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:18:19.162864+00:00
-- url     : https://prove2.me/submissions/69c85fe5-96b3-4fbe-896d-21c7fc8c2fa2

import Mathlib
open MeasureTheory
open scoped NNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (t : ℝ≥0) (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont t] H) :
    StronglyMeasurable[𝓕.rightCont t]
      (fun ω => if τ ω ≤ (t : WithTop ℝ≥0)
        then (0 : ℝ) else H ω)  := by
  have hEvent : MeasurableSet[𝓕.rightCont t]
      {ω : Ω | τ ω ≤ (t : WithTop ℝ≥0)} :=
    hStop t
  exact StronglyMeasurable.ite hEvent stronglyMeasurable_const hH
