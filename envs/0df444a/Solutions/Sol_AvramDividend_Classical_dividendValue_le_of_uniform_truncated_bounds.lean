-- Prove2me | solution 1 for AvramDividend.Classical.dividendValue_le_of_uniform_truncated_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:17:52.248822+00:00
-- url     : https://prove2.me/submissions/4a3c6237-0ca6-4cff-b2ff-22f48ef903d0

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

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
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissible X x D) (A : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ A) :
    dividendValue X q x D ≤ A := by
  rw [dividendValue_eq_iSup_truncated X q x D hD]
  exact iSup_le hBound
