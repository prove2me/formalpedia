-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit1_capped_and_unrestricted_values_eq_iSup_closed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T00:02:03.005758+00:00
-- url     : https://prove2.me/submissions/9a0dae95-5b86-460e-ba2c-8c7940363d82

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact capped and original value suprema over the original Stieltjes
    cash at closed integer horizons, retaining zero and horizon atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (C : ℝ≥0∞) (x : ℝ) :
    (valueFunctionLe X q C x =
      ⨆ D : ℝ≥0 → Ω → ℝ, ⨆ hD : IsAdmissibleLe X x C D, ⨆ n : ℕ,
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P)) ∧
    (valueFunction X q x =
      ⨆ D : ℝ≥0 → Ω → ℝ, ⨆ hD : IsAdmissible X x D, ⨆ n : ℕ,
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P)) := by
  constructor
  · unfold valueFunctionLe
    refine iSup_congr fun D => ?_
    refine iSup_congr fun hD => ?_
    exact dividendValue_eq_iSup_truncated X q x D hD.1
  · unfold valueFunction
    refine iSup_congr fun D => ?_
    refine iSup_congr fun hD => ?_
    exact dividendValue_eq_iSup_truncated X q x D hD
