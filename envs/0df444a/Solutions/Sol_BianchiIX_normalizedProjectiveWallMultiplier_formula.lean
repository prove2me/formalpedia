-- Prove2me | solution 1 for BianchiIX.normalizedProjectiveWallMultiplier_formula
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:25:14.467702+00:00
-- url     : https://prove2.me/submissions/72cb67c2-894d-4fb2-be40-84644c351779

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveWallMultipliers
import Theorems.Thm_BianchiIX_normalized_wall_formula
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open BianchiIX
open Set MeasureTheory


theorem solution {x : NormalizedState} {T : ℝ}
    (hT : T ∈ normalizedMaxDomain x 0) (hA0 : 0 < 1 + x 0)
    (hAT : 0 < 1 + normalizedMaxCurve x 0 T 0) (i : Fin 3) :
    toProjectiveState (normalizedMaxCurve x 0 T) i.succ =
      toProjectiveState x i.succ * normalizedProjectiveWallMultiplier x T i := by
  have H := normalized_wall_formula (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
    (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain x 0) hT i
  rw [normalizedMaxCurve_initial] at H
  have hcoord (z : NormalizedState) : toProjectiveState z i.succ = Real.sqrt 3 * wallValue i z / (1 + z 0) := by
    fin_cases i <;> rfl
  rw [hcoord, hcoord, H, normalizedProjectiveWallMultiplier, Real.exp_add, Real.exp_sub,
    Real.exp_log hA0, Real.exp_log hAT]
  field_simp
