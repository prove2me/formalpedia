-- Prove2me | solution 1 for BianchiIX.compactCoreFactor_transverse_differential
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:27:53.585214+00:00
-- url     : https://prove2.me/submissions/c0770df4-f251-44e6-93ec-0c047b94b53c

import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_Dynamics_CompactCoreFactors
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


theorem solution {Y : CoreAngleState} (i : Fin 2)
    (hF : DifferentiableAt ℝ (coreReturnState coreRadiusReturnTime) Y)
    (hm : DifferentiableAt ℝ (fun Z => compactCoreFactor Z i) Y)
    (hpos : 0 < compactCoreFactor Y i)
    (hnear : ∀ᶠ Z in 𝓝 Y,
      coreReturnState coreRadiusReturnTime Z i.succ = Z i.succ * compactCoreFactor Z i)
    (v : CoreAngleState) :
    (fderiv ℝ (coreReturnState coreRadiusReturnTime) Y v) i.succ = compactCoreFactor Y i *
      (v i.succ + Y i.succ * fderiv ℝ (fun Z => Real.log (compactCoreFactor Z i)) Y v) := by
  have hprod := (hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).mul hm.hasFDerivAt
  change HasFDerivAt (fun Z => Z i.succ * compactCoreFactor Z i) _ Y at hprod
  change (fun Z => coreReturnState coreRadiusReturnTime Z i.succ) =ᶠ[𝓝 Y]
    (fun Z => Z i.succ * compactCoreFactor Z i) at hnear
  have H := congrArg (fun L : CoreAngleState →L[ℝ] ℝ => L v)
    (hnear.fderiv_eq.trans hprod.fderiv)
  rw [fderiv_apply hF i.succ] at H
  rw [(hm.hasFDerivAt.log (ne_of_gt hpos)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    add_apply, smul_apply, smul_eq_mul] at H ⊢
  rw [H]
  field_simp [ne_of_gt hpos]
  ring
