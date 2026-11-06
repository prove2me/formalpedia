-- Prove2me | solution 1 for BianchiIX.compactCoreFactor_reference_value
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:46:57.961689+00:00
-- url     : https://prove2.me/submissions/586eb6dd-541e-4004-b17b-881799562cac

import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_CompactCoreFactors
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_regular
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_wall_derivative
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.coordinateFactor_of_zero {n : ℕ} (f : (Fin n → ℝ) → ℝ) (i : Fin n) {Y : Fin n → ℝ}
    (hY : Y i = 0) : coordinateFactor f i Y = fderiv ℝ f Y (Pi.single i 1) := by
  have hseg (s : ℝ) : coordinateSegment i Y s = Y := by
    simp only [coordinateSegment, hY, mul_zero]
    exact Function.update_eq_self_iff.mpr hY.symm
  simp [coordinateFactor, hseg]

end
end

theorem solution {k : ℝ} (hk : 1 < k) (i : Fin 2) :
    compactCoreFactor ![k, 0, 0] i =
      if i = 0 then Real.exp (-k * Real.arcosh k) else Real.exp (-4 * Real.arcosh k / k) := by
  have hc := (coreRadiusReturn_reference_regular hk).2.2.1
  have hzero : (![k, 0, 0] : CoreAngleState) i.succ = 0 := by fin_cases i <;> rfl
  rw [compactCoreFactor, coordinateFactor_of_zero _ _ hzero]
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) i.succ (coreReturnState coreRadiusReturnTime ![k, 0, 0])).comp
    (![k, 0, 0] : CoreAngleState) (hc.differentiableAt (by norm_num)).hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  fin_cases i
  · simpa using (coreRadiusReturn_reference_wall_derivative hk (Pi.single 1 1)).1
  · simpa using (coreRadiusReturn_reference_wall_derivative hk (Pi.single 2 1)).2
