-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_uniform_bound_dominates_exact_reflected_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:34:15.754571+00:00
-- url     : https://prove2.me/submissions/06bcf37d-b353-42a0-8965-e91730543fcd

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_first_jump_payout
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Any common finite-horizon bound must dominate the exact infinite-horizon
zero-cap reflected value in the original finite-jump-activity BV source. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ)
    (hUniform : ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤
      ENNReal.ofReal W) :
    ENNReal.ofReal
      (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) ≤
    ENNReal.ofReal W := by
  have hD : IsAdmissibleLe X 0 0 (barrierStrategy X 0 0) := by
    simpa only [ENNReal.ofReal_zero] using
      (barrierStrategy_admissibleLe_nonnegative_barrier
        X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
  have hb := dividendValue_le_of_uniform_truncated_bounds
    X q 0 (barrierStrategy X 0 0) hD.1
      (ENNReal.ofReal W) hUniform
  rw [barrierValue_self_eq_barrierSupValue,
    bv_finite_activity_zero_reflected_first_jump_payout
      X hX q hq hBV hFinite] at hb
  exact hb
