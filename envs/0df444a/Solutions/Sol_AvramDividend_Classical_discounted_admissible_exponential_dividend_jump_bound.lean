-- Prove2me | solution 1 for AvramDividend.Classical.discounted_admissible_exponential_dividend_jump_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:41:28.673766+00:00
-- url     : https://prove2.me/submissions/78a22963-0d29-4c6c-9258-2694e7b86fc3

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_exponential_dividend_jump_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (θ q : ℝ) (hθ : 1 ≤ θ)
    (ω : Ω) (t : ℝ≥0)
    (ht : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-(q * (t : ℝ))) * (rightLimit D t ω - D t ω) ≤
      Real.exp (-(q * (t : ℝ))) *
        (Real.exp (θ * riskProcess X x D t ω) -
          Real.exp (θ * (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))) := by
  exact mul_le_mul_of_nonneg_left
    (admissible_exponential_dividend_jump_bound X x D hD θ hθ ω t ht)
    (Real.exp_pos _).le
