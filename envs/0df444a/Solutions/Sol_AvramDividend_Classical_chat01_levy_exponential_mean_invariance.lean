-- Prove2me | solution 1 for AvramDividend.Classical.chat01_levy_exponential_mean_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:31:50.010724+00:00
-- url     : https://prove2.me/submissions/12c42c35-6f96-4713-a76a-43ded3e6dfbb

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
open AvramDividend.Classical MeasureTheory
open scoped NNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, Real.exp (θ * X.X s w -
      (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) =
    (∫ w, Real.exp (θ * X.X t w -
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) := by
  have hm := AvramDividend.Classical.levy_compensated_exponential_martingale X θ hθ
  have h := hm.2 s t hst
  exact (integral_congr_ae h).symm.trans (integral_condExp (𝓕.le s))
