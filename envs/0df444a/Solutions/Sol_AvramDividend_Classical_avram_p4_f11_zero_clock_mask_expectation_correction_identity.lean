-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_zero_clock_mask_expectation_correction_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:02:42.552072+00:00
-- url     : https://prove2.me/submissions/f2c40887-60b8-450f-90bb-8c174b0a49b0

import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- Exact zero-clock mask correction on the original finite probability space. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    [DecidablePred (fun ω : Ω => ω ∈ A)]
    (F : Ω → ℝ) (hF : Integrable F P) (b : ℝ) :
    (∫ ω, (if ω ∈ A then b else F ω) ∂P) =
      (∫ ω, F ω ∂P) + ∫ ω in A, b - F ω ∂P := by
  have hb : Integrable (fun _ : Ω => b) P := integrable_const b
  have hI : Integrable (A.indicator (fun ω => b - F ω)) P :=
    (hb.sub hF).indicator hA
  have hfun : (fun ω => if ω ∈ A then b else F ω) =
      (fun ω => F ω + A.indicator (fun ω => b - F ω) ω) := by
    funext ω
    by_cases h : ω ∈ A
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  rw [hfun, integral_add hF hI]
  rw [MeasureTheory.integral_indicator hA]
