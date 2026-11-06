-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_top_cap_real_stieltjes_sup_eq_unrestricted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T09:56:57.979685+00:00
-- url     : https://prove2.me/submissions/0f854025-3f2b-4417-9793-af0c6c7dbc2b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- At the unrestricted top cap, the literal original capped admissible
    strategies give exactly the original unrestricted real payout supremum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ) :
    (⨆ (D : ℝ≥0 → Ω → ℝ),
      ⨆ (_ : IsAdmissibleLe X x (⊤ : ℝ≥0∞) D),
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)) =
    (⨆ (D : ℝ≥0 → Ω → ℝ),
      ⨆ (_ : IsAdmissible X x D),
        ENNReal.ofReal
          (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P)) := by
  simp [IsAdmissibleLe]
