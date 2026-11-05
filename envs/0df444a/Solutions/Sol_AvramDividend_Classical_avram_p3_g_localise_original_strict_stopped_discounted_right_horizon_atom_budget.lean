-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_g_localise_original_strict_stopped_discounted_right_horizon_atom_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:54:03.313469+00:00
-- url     : https://prove2.me/submissions/0466b001-f6a4-4546-955c-84f38cfc1ce6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Canonical strict stopping preserves the genuine right-horizon
discounted dividend-atom plus postpayment terminal inequality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) :
    ∀ (ω : Ω) (t : ℝ≥0),
      (if (t : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (t : ℝ))) *
            (rightLimit D t ω - D t ω) +
          Real.exp (-(q * (t : ℝ))) *
            w (x + X.X t ω - rightLimit D t ω)
       else 0) ≤
      (if (t : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * (t : ℝ))) *
          w (riskProcess X x D t ω)
       else 0) := by
  intro ω t
  by_cases hPre : (t : ℝ≥0∞) < ruinTime X x D ω
  · simpa only [if_pos hPre] using
      (avram_p3_g_localise_original_discounted_right_horizon_jump_atom_budget
        X x D w q hjump ω t (Or.inr hPre))
  · simp only [if_neg hPre, le_refl]
