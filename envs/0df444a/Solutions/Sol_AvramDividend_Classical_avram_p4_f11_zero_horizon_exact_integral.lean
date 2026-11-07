-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f11_zero_horizon_exact_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:47:08.334602+00:00
-- url     : https://prove2.me/submissions/e530948e-01f4-4446-be27-945368ff9f97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At a zero horizon the original three-way stopped payoff is exactly the initial value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (b : ℝ) :
    let τ : Ω → ℝ≥0∞ := fun ω =>
      min (twoSidedExitUpTimeCorrected X (b - 1) ω)
        (min (twoSidedExitDownTimeCorrected X (-1) ω) (0 : ℝ≥0∞))
    (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
        w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) = w 1 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hτ : ∀ ω : Ω,
      min (twoSidedExitUpTimeCorrected X (b - 1) ω)
        (min (twoSidedExitDownTimeCorrected X (-1) ω) (0 : ℝ≥0∞)) = 0 := by
    intro ω
    simp
  simp [hτ, X.X_zero]
