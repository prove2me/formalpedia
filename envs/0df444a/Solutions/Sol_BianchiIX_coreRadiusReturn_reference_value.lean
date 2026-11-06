-- Prove2me | solution 1 for BianchiIX.coreRadiusReturn_reference_value
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T03:37:08.275536+00:00
-- url     : https://prove2.me/submissions/0bf096e9-881c-47c1-8423-7237b3eae7ce

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Theorems.Thm_BianchiIX_coreRadiusReturn_reference_regular
import Theorems.Thm_BianchiIX_referenceNormalizedTime_pos
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_energy
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_referencePulse_exit
import Theorems.Thm_BianchiIX_referencePulse_normalized_crossing
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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

private theorem BianchiIX.referenceExitState_projective (k : ℝ) :
    toProjectiveState (referenceExitState k) = referencePulse k (referenceHalfTime k) :=
  toProjectiveState_fromProjectiveState (ne_of_gt (referencePulse_denom_pos k _))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.referenceEntryState_crossing {k : ℝ} (hk : 1 < k) :
    referenceNormalizedTime k ∈ normalizedMaxDomain (referenceEntryState k) 0 ∧
    normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k) = referenceExitState k := by
  have H := referencePulse_normalized_crossing hk
  refine ⟨?_, ?_⟩
  · simpa only [referenceEntryState, referencePulse_entry hk] using
      H.1 ⟨(referenceNormalizedTime_pos hk).le, le_rfl⟩
  · simpa only [referenceEntryState, referenceExitState, referencePulse_entry hk,
      referencePulse_exit hk] using H.2.1

end
end

theorem solution {k : ℝ} (hk : 1 < k) :
    coreReturnState coreRadiusReturnTime ![k, 0, 0] = ![k, 0, 0] := by
  have hT := (coreRadiusReturn_reference_regular hk).1
  have hx : fromProjectiveState (coreRadiusEntry ![k, 0, 0]) = referenceEntryState k := by
    unfold referenceEntryState
    rw [referencePulse_entry hk]
    rfl
  unfold coreReturnState projectiveOriginalFlow
  rw [hT, hx, (referenceEntryState_crossing hk).2, referenceExitState_projective]
  ext i
  fin_cases i
  · change Real.sqrt (coreEnergy (referencePulse k (referenceHalfTime k) 0)
      (referencePulse k (referenceHalfTime k) 2)) = k
    rw [referencePulse_energy, Real.sqrt_sq (by linarith only [hk])]
  · rfl
  · simp [toCoreAngleState, referencePulse]
