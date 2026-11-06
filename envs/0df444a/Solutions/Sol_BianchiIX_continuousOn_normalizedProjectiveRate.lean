-- Prove2me | solution 1 for BianchiIX.continuousOn_normalizedProjectiveRate
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:25:14.80081+00:00
-- url     : https://prove2.me/submissions/c9c54699-c276-4848-9219-d16eefd26c93

import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology


theorem solution (x : NormalizedState) (t₀ : ℝ) :
    ContinuousOn (normalizedProjectiveRate x t₀) (normalizedMaxDomain x t₀) := by
  intro t ht
  exact (continuousAt_const.add
    ((continuous_apply 0).continuousAt.comp
      (hasDerivAt_normalizedMaxCurve ht).continuousAt)).continuousWithinAt
