-- Prove2me | solution 1 for AvramDividend.Classical.chat04_stopped_scale_exit_payoff_le_total_mass_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:51:38.951799+00:00
-- url     : https://prove2.me/submissions/09f70965-ee6e-42d8-8b59-5443a5a88343

import Mathlib.Tactic.GCongr
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_stopped_scale_exit_payoff_le_upperfirst_mass_any_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal

/-- A uniform stopped scale payoff bound by total path-law mass times barrier scale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a x : ℝ) (hq : 0 ≤ q) (hxa : x ≤ a) (W : ℝ → ℝ) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) ≤
      μ Set.univ * ENNReal.ofReal (W a) := by
  calc
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω)))) *
          ENNReal.ofReal
            (W (x + X.X (twoSidedExitUpTime X (a - x) ω).toNNReal ω))
      else 0 ∂μ) ≤
      μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω} * ENNReal.ofReal (W a) :=
        chat04_stopped_scale_exit_payoff_le_upperfirst_mass_any_measure
          X μ q a x hq hxa W
    _ ≤ μ Set.univ * ENNReal.ofReal (W a) := by
      have hmass : μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
          twoSidedExitDownTime X (-x) ω} ≤ μ Set.univ :=
        measure_mono (Set.subset_univ _)
      gcongr
      all_goals exact hmass
