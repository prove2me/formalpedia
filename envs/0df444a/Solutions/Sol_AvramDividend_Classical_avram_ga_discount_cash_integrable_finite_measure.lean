-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_discount_cash_integrable_finite_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:36:33.75372+00:00
-- url     : https://prove2.me/submissions/93228996-7f0b-4470-950f-d66e28e059b4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ]
    (F Occ Z : Ω → ℝ) (a b c : ℝ)
    (hFI : Integrable F μ) (hOcc : Integrable Occ μ)
    (hZI : Integrable Z μ) :
    Integrable (fun ω => F ω - a - (b + c * Occ ω) - Z ω) μ := by
  have h0 : Integrable (fun ω => F ω - a) μ :=
    hFI.sub (integrable_const (μ := μ) a)
  have h1 : Integrable (fun ω => b + c * Occ ω) μ :=
    (integrable_const (μ := μ) b).add (hOcc.const_mul c)
  exact (h0.sub h1).sub hZI
