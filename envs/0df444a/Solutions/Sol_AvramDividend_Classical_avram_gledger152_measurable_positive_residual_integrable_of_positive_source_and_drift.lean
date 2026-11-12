-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger152_measurable_positive_residual_integrable_of_positive_source_and_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:30:51.040758+00:00
-- url     : https://prove2.me/submissions/191cf962-e51a-438e-aa07-df9835b99ff8

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f g : Ω → ℝ)
    (hfplus : Integrable (fun ω => max (f ω) (0 : ℝ)) P)
    (hfmeas : AEStronglyMeasurable f P)
    (hg : Integrable g P) :
    Integrable (fun ω => max (f ω - g ω) (0 : ℝ)) P := by
  have hmeas : AEStronglyMeasurable
      (fun ω => max (f ω - g ω) (0 : ℝ)) P :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable
      (hfmeas.sub hg.aestronglyMeasurable)
  have hpoint (ω : Ω) :
      max (f ω - g ω) (0 : ℝ) ≤ max (f ω) 0 + |g ω| := by
    apply max_le_iff.mpr
    constructor
    · have h₁ : f ω ≤ max (f ω) (0 : ℝ) := le_max_left _ _
      have h₂ : -(g ω) ≤ |g ω| := neg_le_abs _
      linarith
    · have h₁ : 0 ≤ max (f ω) (0 : ℝ) := le_max_right _ _
      linarith [abs_nonneg (g ω)]
  have hB : Integrable
      (fun ω => max (f ω) (0 : ℝ) + |g ω|) P := hfplus.add hg.abs
  apply Integrable.mono' hB hmeas
  filter_upwards [] with ω
  have h₁ : 0 ≤ max (f ω - g ω) (0 : ℝ) := le_max_right _ _
  have h₂ : 0 ≤ max (f ω) (0 : ℝ) + |g ω| :=
    add_nonneg (le_max_right _ _) (abs_nonneg _)
  simpa only [Real.norm_eq_abs, abs_of_nonneg h₁, abs_of_nonneg h₂]
    using hpoint ω
