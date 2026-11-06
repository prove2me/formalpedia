-- Prove2me | solution 1 for BianchiIX.coreTailEntry_of_exit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:22:00.243037+00:00
-- url     : https://prove2.me/submissions/df3ebfb1-96cc-4930-bd58-2ced15f8e914

import Definitions.Def_BianchiIX_Dynamics_CoreTail
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
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

/-- This chart recovers the actual state on every downward core exit. -/
theorem solution {y : ProjectiveState} (hM : y 0 < 1) (hV : y 2 = 1) :
    coreTailEntry (toCoreAngleState y) = y := by
  have hs : (toCoreAngleState y 0) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    change coreRadius (y 0) (y 2) ^ 2 - 1 = _
    rw [coreRadius_sq, hV]
    dsimp [coreEnergy]
    ring
  ext i
  fin_cases i
  · change 1 - Real.sqrt ((toCoreAngleState y 0) ^ 2 - 1) = y 0
    rw [hs, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hM] : y 0 - 1 < 0)]
    ring
  · rfl
  · exact hV.symm
  · change y 2 * y 3 = y 3
    rw [hV, one_mul]
