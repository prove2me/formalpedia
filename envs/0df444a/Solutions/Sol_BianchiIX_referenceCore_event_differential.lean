-- Prove2me | solution 1 for BianchiIX.referenceCore_event_differential
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:47:10.062726+00:00
-- url     : https://prove2.me/submissions/448aecad-1a5e-4f60-827d-b957a5e106e5

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_projective_event_differential
import Theorems.Thm_BianchiIX_referenceCoreGap_pos
import Theorems.Thm_BianchiIX_referenceExitProjection_eq
import Theorems.Thm_BianchiIX_referenceNormalizedTime_pos
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_referencePulse_exit
import Theorems.Thm_BianchiIX_referencePulse_exit_field
import Theorems.Thm_BianchiIX_referencePulse_normalized_crossing
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.referenceExitState_clock_pos (k : ℝ) : 0 < 1 + referenceExitState k 0 :=
  fromProjectiveState_clock_pos (referencePulse_denom_pos k _)

private theorem BianchiIX.referenceExitState_constraint (k : ℝ) : stateConstraint (referenceExitState k) = 1 :=
  fromProjectiveState_constraint (ne_of_gt (referencePulse_denom_pos k _))

private theorem BianchiIX.referenceExitState_projective (k : ℝ) :
    toProjectiveState (referenceExitState k) = referencePulse k (referenceHalfTime k) :=
  toProjectiveState_fromProjectiveState (ne_of_gt (referencePulse_denom_pos k _))

private theorem BianchiIX.referenceEntryState_crossing {k : ℝ} (hk : 1 < k) :
    referenceNormalizedTime k ∈ normalizedMaxDomain (referenceEntryState k) 0 ∧
    normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k) = referenceExitState k := by
  have H := referencePulse_normalized_crossing hk
  refine ⟨?_, ?_⟩
  · simpa only [referenceEntryState, referencePulse_entry hk] using
      H.1 ⟨(referenceNormalizedTime_pos hk).le, le_rfl⟩
  · simpa only [referenceEntryState, referenceExitState, referencePulse_entry hk,
      referencePulse_exit hk] using H.2.1

theorem solution {k : ℝ} (hk : 1 < k) (v : NormalizedState) :
    fderiv ℝ toProjectiveState (referenceExitState k)
      (normalizedEventDifferential projectiveActiveWall (referenceEntryState k) 0
        (referenceNormalizedTime k) v) =
      referenceExitProjection k (fderiv ℝ toProjectiveState (referenceExitState k)
        (normalizedFlowDifferential (referenceEntryState k) 0 (referenceNormalizedTime k) v)) := by
  have he := (referenceEntryState_crossing hk).2
  have hA : 1 + normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k) 0 ≠ 0 := by
    rw [he]
    exact ne_of_gt (referenceExitState_clock_pos k)
  have hc : stateConstraint (normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k)) = 1 := by
    rw [he]
    exact referenceExitState_constraint k
  have hv : projectiveField (toProjectiveState
      (normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k))) 2 ≠ 0 := by
    rw [he, referenceExitState_projective, referencePulse_exit_field hk]
    exact neg_ne_zero.mpr (ne_of_gt (referenceCoreGap_pos hk))
  have H := projective_event_differential hA hc hv v
  dsimp only at H
  rw [he, referenceExitState_projective] at H
  rw [referenceExitProjection_eq hk]
  exact H
