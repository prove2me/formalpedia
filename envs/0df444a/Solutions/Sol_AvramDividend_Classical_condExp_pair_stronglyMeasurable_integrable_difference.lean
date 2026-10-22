-- Prove2me | solution 1 for AvramDividend.Classical.condExp_pair_stronglyMeasurable_integrable_difference
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T18:39:25.301446+00:00
-- url     : https://prove2.me/submissions/ea04cc6c-6482-4f2a-972d-1aa70746b7ee



import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (F G : Ω → ℝ) :
    StronglyMeasurable (P[F | m]) ∧
    StronglyMeasurable (P[G | m]) ∧
    Integrable (fun ω => (P[F | m]) ω - (P[G | m]) ω) P := by
  have hFM : StronglyMeasurable[m] (P[F | m]) :=
    stronglyMeasurable_condExp
  have hGM : StronglyMeasurable[m] (P[G | m]) :=
    stronglyMeasurable_condExp
  have hFI : Integrable (P[F | m]) P := integrable_condExp
  have hGI : Integrable (P[G | m]) P := integrable_condExp
  exact ⟨hFM, hGM, hFI.sub hGI⟩


