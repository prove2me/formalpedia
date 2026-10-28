-- Prove2me | solution 1 for FeynmanKac.classical_solution_representation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T19:03:21.118161+00:00
-- url     : https://prove2.me/submissions/3b0992cc-3713-42a6-8b61-9e4012d73edd

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_FeynmanKac_PathDiscount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_FeynmanKac_discounted_reward_expectation

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hgrad : m.SquareIntegrableDiscountedGradient u) :
    u m.initialState m.initialTime =
      ∫ ω, (m.pathDiscount m.terminalTime ω *
          m.terminalPayoff (m.path m.terminalTime ω) +
        ∫ s in m.initialTime..m.terminalTime,
          m.pathDiscount s ω * m.runningSource (m.path s ω) s)
        ∂P := by
  rw [← FeynmanKac.discounted_reward_expectation P m u hu hgrad]
  congr 1
  funext ω
  simp only [FeynmanKac.BoundedDiffusionModel.discountedReward, FeynmanKac.discountedReward,
    FeynmanKac.BoundedDiffusionModel.pathDiscount, hu.2.2.1]
