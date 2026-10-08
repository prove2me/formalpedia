-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_le_of_nat_horizon_bounds_of_strategy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T11:32:56.154727+00:00
-- url     : https://prove2.me/submissions/207e8a63-2d41-4746-b51e-a5238ab1232c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_nat_horizon_dividend_payoff_mct_hypotheses_of_strategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (B : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
          paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by
  rcases nat_horizon_dividend_payoff_mct_hypotheses_of_strategy X q x D hD with
    ⟨hmeas, hmono, htend⟩
  have hlim := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htend
  unfold dividendValue
  exact le_of_tendsto hlim (Filter.Eventually.of_forall hbound)
