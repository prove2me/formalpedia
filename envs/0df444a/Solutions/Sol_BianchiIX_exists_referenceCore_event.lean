-- Prove2me | solution 1 for BianchiIX.exists_referenceCore_event
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:48:15.57003+00:00
-- url     : https://prove2.me/submissions/97a9d890-63b1-4230-8455-195627fb648f

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv_field
import Theorems.Thm_BianchiIX_referenceCoreGap_pos
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

private theorem BianchiIX.referenceExitState_rate_neg {k : ℝ} (hk : 1 < k) :
    fderiv ℝ projectiveActiveWall (referenceExitState k) (normalizedField (referenceExitState k)) < 0 := by
  rw [projectiveActiveWall_fderiv_field (ne_of_gt (referenceExitState_clock_pos k))
    (referenceExitState_constraint k), referenceExitState_projective, referencePulse_exit_field hk]
  exact mul_neg_of_pos_of_neg (referenceExitState_clock_pos k) (neg_neg_of_pos (referenceCoreGap_pos hk))

/-- This event is built from the actual original flow and has its genuine initial-state derivative. -/
theorem solution {k : ℝ} (hk : 1 < k) :
    ∃ tau : NormalizedState → ℝ,
      tau (referenceEntryState k) = referenceNormalizedTime k ∧
      ContDiffAt ℝ 1 tau (referenceEntryState k) ∧
      HasFDerivAt tau
        (normalizedEventTimeDifferential projectiveActiveWall (referenceEntryState k) 0
          (referenceNormalizedTime k)) (referenceEntryState k) ∧
      (∀ᶠ y in 𝓝 (referenceEntryState k), tau y ∈ normalizedMaxDomain y 0 ∧
        projectiveActiveWall (normalizedMaxCurve y 0 (tau y)) = 1) ∧
      (∀ᶠ z : NormalizedState × ℝ in 𝓝 (referenceEntryState k, referenceNormalizedTime k),
        z.2 ∈ normalizedMaxDomain z.1 0 ∧
        (projectiveActiveWall (normalizedMaxCurve z.1 0 z.2) = 1 ↔ tau z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y 0 (tau y)) (referenceEntryState k) ∧
      HasFDerivAt (fun y => normalizedMaxCurve y 0 (tau y))
        (normalizedEventDifferential projectiveActiveWall (referenceEntryState k) 0
          (referenceNormalizedTime k)) (referenceEntryState k) := by
  have he := (referenceEntryState_crossing hk).2
  have hg : ContDiffAt ℝ 1 projectiveActiveWall
      (normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k)) := by
    rw [he]
    exact contDiffAt_projectiveActiveWall 1 (ne_of_gt (referenceExitState_clock_pos k))
  have hr : normalizedEventRate projectiveActiveWall (referenceEntryState k) 0
      (referenceNormalizedTime k) ≠ 0 := by
    unfold normalizedEventRate
    rw [he]
    exact ne_of_lt (referenceExitState_rate_neg hk)
  have hv : projectiveActiveWall
      (normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k)) = 1 := by
    rw [he]
    unfold projectiveActiveWall
    rw [referenceExitState_projective, referencePulse_exit hk]
    rfl
  obtain ⟨tau, hinit, hreg, hdt, hhit, huniq, hmap, hdmap⟩ :=
    exists_normalized_event (referenceEntryState_crossing hk).1 hg hr
  exact ⟨tau, hinit, hreg, hdt, by simpa only [hv] using hhit,
    by simpa only [hv] using huniq, hmap, hdmap⟩
