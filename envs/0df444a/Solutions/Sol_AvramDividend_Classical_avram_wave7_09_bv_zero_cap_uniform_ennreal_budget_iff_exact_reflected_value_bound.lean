-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_uniform_ennreal_budget_iff_exact_reflected_value_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:29:37.452662+00:00
-- url     : https://prove2.me/submissions/16f8cc11-fdf6-4ab8-a29e-2b7d2a987b08

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_every_finite_horizon_below_exact_reflected_value
import Theorems.Thm_AvramDividend_Classical_dividendValue_le_of_uniform_truncated_bounds
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_first_jump_payout
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- For all extended nonnegative allowances, including infinity, the
exact original finite-activity BV zero-cap uniform budget threshold is
the original first-jump reflected dividend value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (A : ℝ≥0∞) :
    (∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) ≤ A) ↔
    ENNReal.ofReal
      (X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) ≤ A := by
  constructor
  · intro hUniform
    have hD : IsAdmissibleLe X 0 (0 : ℝ≥0∞) (barrierStrategy X 0 0) := by
      simpa only [ENNReal.ofReal_zero] using
        (barrierStrategy_admissibleLe_nonnegative_barrier
          X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
    have hValue :=
      dividendValue_le_of_uniform_truncated_bounds
        X q 0 (barrierStrategy X 0 0) hD.1 A hUniform
    rw [barrierValue_self_eq_barrierSupValue,
      bv_finite_activity_zero_reflected_first_jump_payout
        X hX q hq hBV hFinite] at hValue
    exact hValue
  · intro hExact n
    exact
      (avram_wave7_09_bv_zero_cap_every_finite_horizon_below_exact_reflected_value
        X hX hBV hFinite q hq n).trans hExact
