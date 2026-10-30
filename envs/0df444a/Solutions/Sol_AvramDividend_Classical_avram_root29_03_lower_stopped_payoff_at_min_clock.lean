-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_lower_stopped_payoff_at_min_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:48:27.902979+00:00
-- url     : https://prove2.me/submissions/8ed10fdf-8176-4aa7-a789-6792cac1e0e0

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- On genuine strict lower-first paths, the two-sided stopped minimum
is exactly the lower exit clock. Therefore any nonnegative lower-branch
reward can be evaluated at that minimum with no creeping hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (g : ℝ≥0∞ → Ω → ℝ≥0∞) :
    (∫⁻ ω, if twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω then
      g (min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω)) ω
    else 0 ∂μ) =
    (∫⁻ ω, if twoSidedExitDownTime X (-x) ω <
        twoSidedExitUpTime X (a - x) ω then
      g (twoSidedExitDownTime X (-x) ω) ω
    else 0 ∂μ) := by
  refine lintegral_congr fun ω => ?_
  by_cases hd : twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a - x) ω
  · have hMin : min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) =
        twoSidedExitDownTime X (-x) ω :=
      min_eq_right (le_of_lt hd)
    simp [hd, hMin]
  · simp [hd]
