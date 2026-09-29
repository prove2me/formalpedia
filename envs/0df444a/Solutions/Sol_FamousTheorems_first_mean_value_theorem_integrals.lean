-- Prove2me | solution 1 for FamousTheorems.first_mean_value_theorem_integrals
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:39:27.596627+00:00
-- url     : https://prove2.me/submissions/dcd1ca5c-8f6d-4da5-a5a0-377f17d50952

import Mathlib

theorem solution {a b : ℝ} {f g : ℝ → ℝ} {μ : MeasureTheory.Measure ℝ} (hf : ContinuousOn f (Set.uIcc a b))
    (hg : IntervalIntegrable g μ a b) (hg0 : ∀ x ∈ Set.uIoc a b, 0 ≤ g x) :
    ∃ c ∈ Set.uIcc a b, ∫ x in a..b, f x * g x ∂μ = f c * ∫ x in a..b, g x ∂μ :=
  exists_eq_const_mul_intervalIntegral_of_nonneg hf hg hg0
