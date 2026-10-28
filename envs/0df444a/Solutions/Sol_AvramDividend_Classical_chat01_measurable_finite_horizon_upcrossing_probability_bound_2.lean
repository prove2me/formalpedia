-- Prove2me | solution 2 for AvramDividend.Classical.chat01_measurable_finite_horizon_upcrossing_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:56:29.492984+00:00
-- url     : https://prove2.me/submissions/a058ec25-9c5f-404e-a944-25d7f3bf7f5a

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat01_finite_horizon_upcrossing_discount_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For measurable finite-horizon first-upcrossing events, the probability
    weighted by the horizon discount is bounded by the Esscher tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (A : Set Ω)
    (hAmeas : MeasurableSet A)
    (hA : A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)})
    (t : ℝ) (htime : ∀ ω ∈ A, ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t) :
    ENNReal.ofReal (Real.exp (-(q * t))) * P A ≤
      ENNReal.ofReal (Real.exp (-(φ * z))) := by
  have h :=
    chat01_finite_horizon_upcrossing_discount_bound
      X q hq φ hφ hroot z hz A hA t htime
  simpa only [lintegral_indicator_const hAmeas] using h
