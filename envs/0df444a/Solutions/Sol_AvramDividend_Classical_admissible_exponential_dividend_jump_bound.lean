-- Prove2me | solution 1 for AvramDividend.Classical.admissible_exponential_dividend_jump_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:22:17.161337+00:00
-- url     : https://prove2.me/submissions/80d289ed-e5a1-4b0f-a4c4-bb61aa2f4d23

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_exponential_dividend_jump_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (θ : ℝ) (hθ : 1 ≤ θ)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    rightLimit D t ω - D t ω ≤
      Real.exp (θ * riskProcess X x D t ω) -
        Real.exp (θ * (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω))) := by
  have hnonneg : 0 ≤ rightLimit D t ω - D t ω :=
    sub_nonneg.mpr (dividendStrategy_le_rightLimit D hD.1 ω t)
  have hcap : rightLimit D t ω - D t ω ≤
      riskProcess X x D t ω := hD.2 ω t ht
  exact exponential_dividend_jump_bound θ
    (riskProcess X x D t ω)
    (rightLimit D t ω - D t ω) hθ hnonneg hcap
