-- Prove2me | solution 1 for AvramDividend.Classical.esscher_exp_process_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:52:27.910979+00:00
-- url     : https://prove2.me/submissions/921cf8e8-c835-4566-9e19-adf598be869d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-! Reuse the established compensated-exponential martingale for the explicit
Lévy-Khintchine exponent in the Esscher first-passage branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ) :
    Martingale
      (fun (t : ℝ≥0) (ω : Ω) =>
        Real.exp (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ))
      𝓕 P := by
  exact levy_compensated_exponential_martingale X θ hθ
