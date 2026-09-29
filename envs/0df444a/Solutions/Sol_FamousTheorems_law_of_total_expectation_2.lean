-- Prove2me | solution 2 for FamousTheorems.law_of_total_expectation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T22:00:34.459595+00:00
-- url     : https://prove2.me/submissions/67fc5295-5c05-4653-bb63-1b9c347908d4

import Mathlib

theorem solution {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {m m₀ : MeasurableSpace α}
    {μ : @MeasureTheory.Measure α m₀} (f : α → E) (hm : m ≤ m₀) [MeasureTheory.SigmaFinite (μ.trim hm)] :
    ∫ x, MeasureTheory.condExp m μ f x ∂μ = ∫ x, f x ∂μ :=
  MeasureTheory.integral_condExp hm
