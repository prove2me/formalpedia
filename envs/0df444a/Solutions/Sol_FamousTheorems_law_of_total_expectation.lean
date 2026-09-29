-- Prove2me | solution 1 for FamousTheorems.law_of_total_expectation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:59:22.357426+00:00
-- url     : https://prove2.me/submissions/7210ae3b-9172-4e6d-b2b8-4f8304066ce3

import Mathlib

theorem solution {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {m m₀ : MeasurableSpace α}
    {μ : @MeasureTheory.Measure α m₀} (f : α → E) (hm : m ≤ m₀) [MeasureTheory.SigmaFinite (μ.trim hm)] :
    ∫ x, MeasureTheory.condExp m μ f x ∂μ = ∫ x, f x ∂μ :=
  MeasureTheory.integral_condExp hm
