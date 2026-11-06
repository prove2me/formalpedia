-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_positive_strict_terminal_budget_to_perpetual_dividendValue
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:02:37.078371+00:00
-- url     : https://prove2.me/submissions/d0044865-1771-4abe-b61a-08d790e84a0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_positive_terminal_budget_to_every_nat_stop
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (B : ℝ≥0∞) (Terminal : ℝ → Ω → ℝ≥0∞)
    (hPositive : ∀ (T : ℝ), 0 < T →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal T ω) ∂P) ≤ B) :
    dividendValue X q x D ≤ B := by
  apply avram_wave6_10_original_natural_stopped_budget_implies_full_dividendValue
    X q x D hD B
  exact avram_limit2_original_strict_positive_terminal_budget_to_every_nat_stop
    X q x D B Terminal hPositive
