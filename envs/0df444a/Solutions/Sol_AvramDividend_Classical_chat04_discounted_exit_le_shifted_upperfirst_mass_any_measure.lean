-- Prove2me | solution 1 for AvramDividend.Classical.chat04_discounted_exit_le_shifted_upperfirst_mass_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:23:50.384494+00:00
-- url     : https://prove2.me/submissions/57661c06-f003-4997-96ce-9dee0f9d127a

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_joint_discounted_exit_any_measure_comparison
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_mass_bound_any_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Under any path-space measure, discounted exit is bounded by the shifted upper-first mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a b x y : ℝ) (hq : 0 ≤ q)
    (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤
    μ {ω : Ω | twoSidedExitUpTime X (b - y) ω <
      twoSidedExitDownTime X (-y) ω} := by
  calc
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤
      (∫⁻ ω,
      if twoSidedExitUpTime X (b - y) ω < twoSidedExitDownTime X (-y) ω then
        ENNReal.ofReal (Real.exp
          (-(0 * ENNReal.toReal (twoSidedExitUpTime X (b - y) ω))))
      else 0 ∂μ) :=
        chat04_joint_discounted_exit_any_measure_comparison
          X μ 0 q a b x y (le_refl 0) hq hxy hrel
    _ ≤ μ {ω : Ω | twoSidedExitUpTime X (b - y) ω <
      twoSidedExitDownTime X (-y) ω} :=
        chat04_discounted_upperfirst_mass_bound_any_measure
          X μ 0 b y (le_refl 0)
