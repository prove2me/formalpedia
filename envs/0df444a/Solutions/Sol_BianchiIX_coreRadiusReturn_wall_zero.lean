-- Prove2me | solution 1 for BianchiIX.coreRadiusReturn_wall_zero
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:29:26.362256+00:00
-- url     : https://prove2.me/submissions/be0e5a31-1b07-4b96-86df-8318b86de586

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.toProjectiveState_wall_sign {x : NormalizedState} (hA : 0 < 1 + x 0) (i : Fin 3) :
    (toProjectiveState x i.succ = 0 ↔ wallValue i x = 0) ∧
      (0 ≤ toProjectiveState x i.succ ↔ 0 ≤ wallValue i x) := by
  have heq : toProjectiveState x i.succ = Real.sqrt 3 * wallValue i x / (1 + x 0) := by
    fin_cases i <;> rfl
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [heq]
  constructor
  · simp only [div_eq_zero_iff, mul_eq_zero, ne_of_gt hsqrt, ne_of_gt hA, false_or, or_false]
  · rw [div_eq_mul_inv, mul_nonneg_iff_of_pos_right (inv_pos.mpr hA), mul_nonneg_iff_of_pos_left hsqrt]

end
end

theorem solution {Y : CoreAngleState} (hvalid : coreRadiusReturnValid Y)
    (i : Fin 2) (hi : Y i.succ = 0) : (coreReturnState coreRadiusReturnTime Y) i.succ = 0 := by
  let x := fromProjectiveState (coreRadiusEntry Y)
  let T := coreRadiusReturnTime Y
  have hT : 0 < T := hvalid.1.1.1
  have hdom : T ∈ normalizedMaxDomain x 0 := hvalid.1.1.2.1
  have hA : 0 < 1 + normalizedMaxCurve x 0 T 0 := (hvalid.2.1 T ⟨hT.le, le_rfl⟩).2
  have hzero (j : Fin 3) (hj : wallValue j x = 0) :
      toProjectiveState (normalizedMaxCurve x 0 T) j.succ = 0 := by
    have H := normalized_wall_sign (convex_normalizedMaxDomain x 0) (isOpen_normalizedMaxDomain x 0)
      (fun _ ht => hasDerivAt_normalizedMaxCurve ht) (initial_mem_normalizedMaxDomain x 0) hdom j
    rw [normalizedMaxCurve_initial] at H
    exact (toProjectiveState_wall_sign hA j).1.mpr (H.1.mpr hj)
  fin_cases i
  · change Y 1 = 0 at hi
    exact hzero 0 (by simp [x, fromProjectiveState, coreRadiusEntry, wallValue, hi])
  · change Y 2 = 0 at hi
    have H := hzero 2 (by simp [x, fromProjectiveState, coreRadiusEntry, wallValue, hi])
    change toProjectiveState (normalizedMaxCurve x 0 T) 3 = 0 at H
    change toProjectiveState (normalizedMaxCurve x 0 T) 2 *
      toProjectiveState (normalizedMaxCurve x 0 T) 3 = 0
    rw [H, mul_zero]
