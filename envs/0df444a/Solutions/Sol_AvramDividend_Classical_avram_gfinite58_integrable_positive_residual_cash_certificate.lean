-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite58_integrable_positive_residual_cash_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T22:57:18.213087+00:00
-- url     : https://prove2.me/submissions/c1d85262-1082-4948-94a7-522e4a6f13aa

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (F M : Ω → ℝ) (a limit : ℝ)
    (hInt : IntegrableOn (fun ω => max (F ω - a - M ω) 0) A P)
    (hMean : (∫ ω in A, max (F ω - a - M ω) 0 ∂P) ≤ limit) :
    ∃ E : Ω → ℝ,
      IntegrableOn E A P ∧
      (∀ᵐ ω ∂(P.restrict A), F ω ≤ a + M ω + E ω) ∧
      (∫ ω in A, max (E ω) 0 ∂P) ≤ limit := by
  refine ⟨fun ω => max (F ω - a - M ω) 0, hInt, ?_, ?_⟩
  · filter_upwards [] with ω
    have h : F ω - a - M ω ≤ max (F ω - a - M ω) 0 :=
      le_max_left _ _
    linarith
  · simpa using hMean
