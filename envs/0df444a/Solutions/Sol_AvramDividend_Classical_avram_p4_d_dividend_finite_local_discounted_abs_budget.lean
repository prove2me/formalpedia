-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_finite_local_discounted_abs_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:35:54.883125+00:00
-- url     : https://prove2.me/submissions/a57d95a0-20be-4c7f-ae67-5f1219995f77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_local_right_remainder_lipschitz_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- A compact-band finite stopped right-payment correction is dominated by its actual discounted cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b : ℝ) (L : ℝ≥0)
    (hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ L)
    (q : ℝ) (ω : Ω) (T : ℝ≥0) (s : Finset ℝ≥0)
    (hstop : ∀ t ∈ s, (t : ℝ) ≤ (T : ℝ))
    (hpre : ∀ t ∈ s, riskProcess X x D t ω ∈ Icc a b)
    (hpost : ∀ t ∈ s,
      x + X.X t ω - rightLimit D t ω ∈ Icc a b) :
    (∑ t ∈ s, |Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω))|) ≤
      ∑ t ∈ s, (1 + (L : ℝ)) * Real.exp (-(q * (t : ℝ))) *
        (rightLimit D t ω - D t ω) := by
  apply Finset.sum_le_sum
  intro t ht
  have hsingle :=
    avram_p4_d_dividend_local_right_remainder_lipschitz_bound
      X x D hD w a b L hDiff hDeriv ω t
      (hpre t ht) (hpost t ht)
  rw [abs_mul, abs_of_nonneg (le_of_lt (Real.exp_pos _))]
  calc
    Real.exp (-(q * (t : ℝ))) *
        |(rightLimit D t ω - D t ω) +
          w (x + X.X t ω - rightLimit D t ω) -
          w (riskProcess X x D t ω)| ≤
      Real.exp (-(q * (t : ℝ))) *
        ((1 + (L : ℝ)) * (rightLimit D t ω - D t ω)) :=
      mul_le_mul_of_nonneg_left hsingle (le_of_lt (Real.exp_pos _))
    _ = (1 + (L : ℝ)) * Real.exp (-(q * (t : ℝ))) *
        (rightLimit D t ω - D t ω) := by ring