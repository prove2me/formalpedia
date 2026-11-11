-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin34_original_initial_event_mask_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:37:40.704036+00:00
-- url     : https://prove2.me/submissions/03cf0882-b54b-424c-ba23-38d876bdad5a

import Mathlib.Probability.Process.Predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable
open Classical MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    IsStronglyPredictable 𝓕.rightCont
      (fun (_ : ℝ≥0) (ω : Ω) => if ω ∈ A then (1 : ℝ) else 0) := by
  have hAdapt : StronglyAdapted 𝓕.rightCont
      (fun (_ : ℝ≥0) (ω : Ω) => if ω ∈ A then (1 : ℝ) else 0) := by
    intro t
    have hStep : (0 : ℝ≥0) ≤ t := bot_le
    have hAt : MeasurableSet[𝓕.rightCont t] A :=
      (𝓕.rightCont.mono hStep) A hA
    exact StronglyMeasurable.ite hAt
      stronglyMeasurable_const stronglyMeasurable_const
  have hLeft : ∀ ω (t : ℝ≥0),
      ContinuousWithinAt
        (fun (_ : ℝ≥0) => if ω ∈ A then (1 : ℝ) else 0) (Iic t) t := by
    intro ω t
    exact continuousWithinAt_const
  exact avram_wave3_04_strongAdapted_leftContinuous_predictable hAdapt hLeft
