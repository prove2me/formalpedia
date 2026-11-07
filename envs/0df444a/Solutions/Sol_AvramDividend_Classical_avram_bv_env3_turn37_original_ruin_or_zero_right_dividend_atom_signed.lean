-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn37_original_ruin_or_zero_right_dividend_atom_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:46:57.952193+00:00
-- url     : https://prove2.me/submissions/d5941029-264c-4447-bd7f-1f97e501bfe4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original right-payment atom cannot increase discounted
    value plus cash, at zero and all strictly pre-ruin times. -/
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
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      Real.exp (-(q * (t : ℝ))) *
        ((rightLimit D t ω - D t ω) +
         w (riskProcess X x D t ω -
           (rightLimit D t ω - D t ω)) -
         w (riskProcess X x D t ω)) ≤ 0 := by
  intro ω t ht
  have hAtom := hjump ω t ht
  have hResidual :
      (rightLimit D t ω - D t ω) +
        w (riskProcess X x D t ω -
          (rightLimit D t ω - D t ω)) -
        w (riskProcess X x D t ω) ≤ 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos
    (Real.exp_pos _).le hResidual
