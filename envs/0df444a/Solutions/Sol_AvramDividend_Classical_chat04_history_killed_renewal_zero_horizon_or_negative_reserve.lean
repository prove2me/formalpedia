-- Prove2me | solution 1 for AvramDividend.Classical.chat04_history_killed_renewal_zero_horizon_or_negative_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T19:04:58.061559+00:00
-- url     : https://prove2.me/submissions/877cc134-c129-4cca-b983-b3aae0f11633

import Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_initial_nonnegative
import Theorems.Thm_AvramDividend_Classical_chat04_killed_survival_lintegral_zero_of_negative_initial_reserve
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The genuine killed renewal identity is exact at time zero or below zero capital. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (t : ℝ≥0) (hBoundary : t = 0 ∨ x < 0) :
    (∫⁻ ω,
      ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
        (fun u => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω ∂P) =
    ENNReal.ofReal (W x) := by
  rcases hBoundary with ht | hx
  · subst t
    by_cases hx0 : 0 ≤ x
    · exact chat04_killed_survival_lintegral_initial_nonnegative X q W x hx0
    · exact chat04_killed_survival_lintegral_zero_of_negative_initial_reserve
        X q W hW x (lt_of_not_ge hx0) 0
  · exact chat04_killed_survival_lintegral_zero_of_negative_initial_reserve
      X q W hW x hx t
