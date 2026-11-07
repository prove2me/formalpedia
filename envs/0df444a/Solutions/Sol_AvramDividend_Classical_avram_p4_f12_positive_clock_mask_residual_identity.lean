-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f12_positive_clock_mask_residual_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:16:56.186379+00:00
-- url     : https://prove2.me/submissions/03d804b9-df84-44b6-8a85-20d3149cb877

import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- The exact signed excess of a zero-clock-masked reward lives on positive clocks. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    [DecidablePred (fun ω : Ω => ω ∈ A)]
    (F : Ω → ℝ) (hF : Integrable F P) (b : ℝ) :
    (∫ ω, (if ω ∈ A then b else F ω) - b ∂P) =
      ∫ ω in Aᶜ, F ω - b ∂P := by
  have hb : Integrable (fun _ : Ω => b) P := integrable_const b
  have hfun : (fun ω => (if ω ∈ A then b else F ω) - b) =
      Aᶜ.indicator (fun ω => F ω - b) := by
    funext ω
    by_cases h : ω ∈ A
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  rw [hfun, MeasureTheory.integral_indicator hA.compl]
