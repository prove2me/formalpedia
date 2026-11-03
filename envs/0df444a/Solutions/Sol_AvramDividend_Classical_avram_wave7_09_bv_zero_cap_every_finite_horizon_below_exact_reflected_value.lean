-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_every_finite_horizon_below_exact_reflected_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:19:56.675833+00:00
-- url     : https://prove2.me/submissions/96660d0f-c871-4a16-9c16-73a21d1d0be5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_first_jump_payout
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every finite horizon of the original source's zero-reserve,
zero-cap reflected dividend strategy is bounded by the exact
positive infinite-horizon first-jump value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (n : ℕ) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
    ENNReal.ofReal
      (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) := by
  have hD : IsAdmissibleLe X 0 (0 : ℝ≥0∞) (barrierStrategy X 0 0) := by
    simpa only [ENNReal.ofReal_zero] using
      (barrierStrategy_admissibleLe_nonnegative_barrier
        X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
  have hBound :
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
      dividendValue X q 0 (barrierStrategy X 0 0) := by
    rw [dividendValue_eq_iSup_truncated X q 0
      (barrierStrategy X 0 0) hD.1]
    exact le_iSup_of_le n le_rfl
  rw [barrierValue_self_eq_barrierSupValue,
    bv_finite_activity_zero_reflected_first_jump_payout
      X hX q hq hBV hFinite] at hBound
  exact hBound
