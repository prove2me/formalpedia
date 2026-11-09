-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_route11_zero_cap_closed_cash_bound_false
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:33:47.026473+00:00
-- url     : https://prove2.me/submissions/7b3b6105-c88a-4080-9411-3a0cc71d356b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_route11_zero_cap_contact_positive_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A genuine zero-cap cash flow excludes a uniform zero cash budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ¬ ∀ T : ℝ, 0 ≤ T →
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
        (0 : ℝ≥0∞) := by
  intro hBudget
  obtain ⟨n, _hAdmissible, _hNoRightJumps, hPositive⟩ :=
    avram_bv_route11_zero_cap_contact_positive_cash
      X hX hBV hFinite q hq
  have hZeroBound := hBudget (n : ℝ) (by positivity)
  exact (not_le_of_gt hPositive) hZeroBound
