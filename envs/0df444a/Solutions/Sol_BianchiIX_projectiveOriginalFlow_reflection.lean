-- Prove2me | solution 1 for BianchiIX.projectiveOriginalFlow_reflection
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:54:26.433676+00:00
-- url     : https://prove2.me/submissions/5fee936b-11f2-4a19-92bf-734adfedd1cf

import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Theorems.Thm_BianchiIX_NormalizedSymmetry_maxCurve
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
open BianchiIX

private theorem BianchiIX.projectiveReflection_denom (y : ProjectiveState) :
    projectiveStateDenom (projectiveReflection y) = projectiveStateDenom y := by
  dsimp [projectiveStateDenom, projectiveDenom, projectiveReflection, curvature]
  ring

private theorem BianchiIX.toProjectiveState_axisSwap (x : NormalizedState) :
    toProjectiveState (axisSwap x) = projectiveReflection (toProjectiveState x) := by
  ext i
  fin_cases i <;> dsimp [toProjectiveState, axisSwap, projectiveReflection, projectiveCoord]
  all_goals ring

private theorem BianchiIX.fromProjectiveState_reflection (y : ProjectiveState) :
    fromProjectiveState (projectiveReflection y) = axisSwap (fromProjectiveState y) := by
  simp only [fromProjectiveState, projectiveReflection_denom]
  ext i
  fin_cases i <;> dsimp [projectiveReflection, axisSwap]
  all_goals ring

theorem solution {y : ProjectiveState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀) :
    projectiveOriginalFlow (projectiveReflection y) t₀ t =
      projectiveReflection (projectiveOriginalFlow y t₀ t) := by
  have H := NormalizedSymmetry.swap.maxCurve ht
  change normalizedMaxCurve (axisSwap (fromProjectiveState y)) t₀ t =
    axisSwap (normalizedMaxCurve (fromProjectiveState y) t₀ t) at H
  simp only [projectiveOriginalFlow, fromProjectiveState_reflection, H, toProjectiveState_axisSwap]
