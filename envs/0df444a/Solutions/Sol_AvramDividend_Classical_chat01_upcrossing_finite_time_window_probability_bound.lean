-- Prove2me | solution 1 for AvramDividend.Classical.chat01_upcrossing_finite_time_window_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:01:19.303228+00:00
-- url     : https://prove2.me/submissions/40884161-7ad8-4d98-84fe-528392438627

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat01_measurable_finite_horizon_upcrossing_probability_bound
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual finite first-upcrossing time window satisfies the uniform
    Esscher exponential probability bound when its event is measurable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (t : ℝ)
    (hWindowMeas : MeasurableSet
      {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞) ∧
        ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t}) :
    ENNReal.ofReal (Real.exp (-(q * t))) *
      P {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞) ∧
        ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t} ≤
      ENNReal.ofReal (Real.exp (-(φ * z))) := by
  exact chat01_measurable_finite_horizon_upcrossing_probability_bound
    X q hq φ hφ hroot z hz
    {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞) ∧
      ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t}
    hWindowMeas (by
      intro ω hω
      exact hω.1) t (by
      intro ω hω
      exact hω.2)
