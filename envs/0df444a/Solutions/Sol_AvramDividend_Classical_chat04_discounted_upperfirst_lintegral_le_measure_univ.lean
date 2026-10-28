-- Prove2me | solution 1 for AvramDividend.Classical.chat04_discounted_upperfirst_lintegral_le_measure_univ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:29:45.699043+00:00
-- url     : https://prove2.me/submissions/9c043f5f-22b3-40fa-aee7-a8077a996b76

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_mass_bound_any_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The killed upper-first discounted reward is bounded by total mass under any law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a x : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤ μ Set.univ := by
  calc
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤
      μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} :=
        chat04_discounted_upperfirst_mass_bound_any_measure X μ q a x hq
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
