-- Prove2me | solution 1 for FeynmanKac.classical_solution_unique
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T21:11:04.858526+00:00
-- url     : https://prove2.me/submissions/a9d5ae68-f418-43c0-9280-92501feb9069

import Definitions.Def_FeynmanKac_ClassicalSolutionConditions
import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Definitions.Def_FeynmanKac_PathDiscount
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_FeynmanKac_discounted_reward_expectation

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P)
    (u v : ℝ → ℝ → ℝ)
    (hu : m.IsClassicalPDESolution u)
    (hv : m.IsClassicalPDESolution v)
    (huGrad : m.SquareIntegrableDiscountedGradient u)
    (hvGrad : m.SquareIntegrableDiscountedGradient v) :
    u m.initialState m.initialTime =
      v m.initialState m.initialTime := by
  rw [← FeynmanKac.discounted_reward_expectation P m u hu huGrad,
    ← FeynmanKac.discounted_reward_expectation P m v hv hvGrad]
  congr 1
  funext ω
  simp only [FeynmanKac.BoundedDiffusionModel.discountedReward, FeynmanKac.discountedReward,
    FeynmanKac.BoundedDiffusionModel.pathDiscount, hu.2.2.1, hv.2.2.1]
