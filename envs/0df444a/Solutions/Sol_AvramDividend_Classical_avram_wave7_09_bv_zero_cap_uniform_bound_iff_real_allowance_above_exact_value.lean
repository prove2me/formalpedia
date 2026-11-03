-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_uniform_bound_iff_real_allowance_above_exact_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:20:50.93944+00:00
-- url     : https://prove2.me/submissions/e716b683-e26d-44ef-94b1-4e3e9f6bb477

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_uniform_real_boundary_at_least_exact_value
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

/-- Sharp if-and-only-if zero-cap original Stieltjes boundary allowance:
uniform horizon boundedness is equivalent to a real first-jump threshold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ) :
    (∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
      ENNReal.ofReal W) ↔
    X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal) ≤ W := by
  constructor
  · intro hUniform
    exact
      avram_wave7_09_bv_finite_activity_zero_cap_uniform_real_boundary_at_least_exact_value
        X hX hBV hFinite q hq W hUniform
  · intro hThreshold n
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
    exact hBound.trans (ENNReal.ofReal_le_ofReal hThreshold)
