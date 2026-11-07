-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn38_original_finite_pre_ruin_dividend_atom_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:47:01.713198+00:00
-- url     : https://prove2.me/submissions/1f30bb3a-37c7-4e39-a481-8f8f3525060d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact finite-tag original atom cash is bounded by all discounted physical
    prepayment-to-postpayment value drops, including the t = 0 atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) :
    ∀ ω (F : Finset ℝ≥0),
      (∀ t ∈ F, t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      (∑ t ∈ F, Real.exp (-(q * (t : ℝ))) *
        (rightLimit D t ω - D t ω)) ≤
      (∑ t ∈ F, Real.exp (-(q * (t : ℝ))) *
        (w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))) := by
  intro ω F hF
  apply Finset.sum_le_sum
  intro t ht
  exact mul_le_mul_of_nonneg_left
    (hjump ω t (hF t ht)) (Real.exp_pos _).le
