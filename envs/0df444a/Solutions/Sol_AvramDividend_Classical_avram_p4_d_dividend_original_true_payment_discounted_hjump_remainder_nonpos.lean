-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_true_payment_discounted_hjump_remainder_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T14:01:53.166474+00:00
-- url     : https://prove2.me/submissions/e436e286-9aa5-4d47-a81b-6c14d223dc2c

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At each original true payment, the actual discounted right-dividend budget is nonpositive,
    using the post-Lévy-jump reserve without swapping jump order. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ℝ≥0)
    (hPay : (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)) :
    Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω)) ≤ 0 := by
  have hEligible : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω := by
    rcases avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
        X x D ω (t : ℝ) hPay with h0 | ⟨_, ht⟩
    · left
      simpa using h0
    · right
      simpa using ht
  have hSec := hjump ω t hEligible
  have hSigned : (rightLimit D t ω - D t ω) +
      w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) -
      w (riskProcess X x D t ω) ≤ 0 := by
    linarith only [hSec]
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos (-(q * (t : ℝ))))) hSigned