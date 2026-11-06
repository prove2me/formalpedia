-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_stopped_discounted_right_dividend_atom_value_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:34:56.779322+00:00
-- url     : https://prove2.me/submissions/66d584bf-c33e-4c59-be0b-d42e953b5f2c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_postpayment_dividend_atom_value_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive discount preserves the original stopped right-payment bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (hTime : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) :
    Real.exp (-(q * (t : ℝ))) *
      w (x + X.X t ω - rightLimit D t ω) +
      Real.exp (-(q * (t : ℝ))) *
        (rightLimit D t ω - D t ω) ≤
      Real.exp (-(q * (t : ℝ))) *
        w (riskProcess X x D t ω) := by
  have hB := avram_p4_f3_original_stopped_postpayment_dividend_atom_value_budget
    X x D hD w hjump ω t hTime
  have hE : 0 ≤ Real.exp (-(q * (t : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have hScaled := mul_le_mul_of_nonneg_left hB hE
  simpa only [mul_add] using hScaled
