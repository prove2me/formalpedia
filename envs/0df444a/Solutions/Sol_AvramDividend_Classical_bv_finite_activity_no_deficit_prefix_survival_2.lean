-- Prove2me | solution 2 for AvramDividend.Classical.bv_finite_activity_no_deficit_prefix_survival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:30:21.353379+00:00
-- url     : https://prove2.me/submissions/7ba3f7ca-c361-4ec8-8ca7-14d4ad2e8155

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_history_zero_exponential_survival

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Swap the factors in the drift residual of the established survival identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
      X.drift * (s : ℝ) - X.X s ω = 0} =
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by
  have hEvent :
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
        X.drift * (s : ℝ) - X.X s ω = 0} =
      {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
        (s : ℝ) * X.drift - X.X s ω = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h s hs
      simpa only [mul_comm (s : ℝ) X.drift] using h s hs
    · intro h s hs
      simpa only [mul_comm X.drift (s : ℝ)] using h s hs
  rw [hEvent]
  exact bv_actual_residual_history_zero_exponential_survival X hBV hFinite t
