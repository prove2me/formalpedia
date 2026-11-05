-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_local_cash_summable_implies_right_remainder_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:23:52.362581+00:00
-- url     : https://prove2.me/submissions/ed8e8a73-3848-4a03-aab4-eb4c78a4fb7a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_local_right_remainder_lipschitz_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- A summable original local discounted cash bound gives an absolutely summable right-dividend residual. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b : ℝ) (L : ℝ≥0)
    (hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ L)
    (ω : Ω) (q : ℝ) (A : Set ℝ≥0)
    (hpre : ∀ t : A, riskProcess X x D (t : ℝ≥0) ω ∈ Icc a b)
    (hpost : ∀ t : A,
      x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω ∈ Icc a b)
    (hcash : Summable (fun t : A =>
      Real.exp (-(q * (((t : ℝ≥0) : ℝ)))) *
        ((1 + (L : ℝ)) *
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)))) :
    Summable (fun t : A =>
      Real.exp (-(q * (((t : ℝ≥0) : ℝ)))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
          w (riskProcess X x D (t : ℝ≥0) ω))) := by
  apply Summable.of_norm_bounded hcash
  intro t
  have hsingle :=
    avram_p4_d_dividend_local_right_remainder_lipschitz_bound
      X x D hD w a b L hDiff hDeriv ω (t : ℝ≥0)
      (hpre t) (hpost t)
  have he : 0 ≤ Real.exp (-(q * (((t : ℝ≥0) : ℝ)))) :=
    le_of_lt (Real.exp_pos _)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg he]
  exact mul_le_mul_of_nonneg_left hsingle he