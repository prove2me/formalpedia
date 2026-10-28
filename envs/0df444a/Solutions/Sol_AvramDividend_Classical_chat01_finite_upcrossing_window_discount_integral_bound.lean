-- Prove2me | solution 1 for AvramDividend.Classical.chat01_finite_upcrossing_window_discount_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:00:17.543992+00:00
-- url     : https://prove2.me/submissions/9667c60e-b863-4f22-b9d3-a984deaa9048

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_chat01_finite_horizon_upcrossing_discount_bound
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Finite-time upcrossing-window discounted mass is bounded by the Esscher tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (t : ℝ) :
    (∫⁻ ω, ({ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞) ∧
      ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t}).indicator
      (fun ω => ENNReal.ofReal (Real.exp (-(q * t)))) ω ∂P) ≤
      ENNReal.ofReal (Real.exp (-(φ * z))) := by
  exact chat01_finite_horizon_upcrossing_discount_bound
    X q hq φ hφ hroot z hz
    {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞) ∧
      ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t}
    (by
      intro ω hω
      exact hω.1) t (by
      intro ω hω
      exact hω.2)
