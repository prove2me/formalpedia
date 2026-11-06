-- Prove2me | solution 1 for BianchiIX.referenceCore_actual_derivative
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:49:17.55447+00:00
-- url     : https://prove2.me/submissions/7695841f-6a35-4b8a-914d-8513db7e4c17

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ReferenceActualVariation
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_referenceClockPrimitive
import Theorems.Thm_BianchiIX_hasDerivAt_referenceOriginalVariation
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_referenceClock_normalized_orbit
import Theorems.Thm_BianchiIX_referenceCore_event_differential
import Theorems.Thm_BianchiIX_referenceNormalizedTime_pos
import Theorems.Thm_BianchiIX_referencePulse_clock_integral
import Theorems.Thm_BianchiIX_referencePulse_crossing_time
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_referencePulse_exit
import Theorems.Thm_BianchiIX_referencePulse_normalized_crossing
import Theorems.Thm_BianchiIX_referenceVariation_scattering
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
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
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.normalizedFlowDifferential_initial (x : NormalizedState) (t₀ : ℝ) :
    normalizedFlowDifferential x t₀ t₀ = ContinuousLinearMap.id ℝ NormalizedState := by
  simp [normalizedFlowDifferential, normalizedMaxCurve_initial]

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

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveFlowDifferential_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveFlowDifferential y t₀ t₀ = ContinuousLinearMap.id ℝ ProjectiveState := by
  rw [projectiveFlowDifferential, normalizedMaxCurve_initial, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp, projective_chart_differential_inverse hD]

end
end

private theorem BianchiIX.hasDerivAt_referenceClock (k t : ℝ) :
    HasDerivAt (referenceClock k) (projectiveStateDenom (referencePulse k t) / 6) t :=
  (hasDerivAt_referenceClockPrimitive k t).sub_const _

private theorem BianchiIX.referenceClock_entry (k : ℝ) : referenceClock k (-referenceHalfTime k) = 0 := sub_self _

private theorem BianchiIX.referenceClock_exit (k : ℝ) :
    referenceClock k (referenceHalfTime k) = referenceNormalizedTime k := by
  rw [referenceClock, ← referencePulse_clock_integral, referencePulse_crossing_time]

private theorem BianchiIX.referenceClock_projective_orbit (k t : ℝ) :
    projectiveOriginalFlow (referencePulse k (-referenceHalfTime k)) 0 (referenceClock k t) =
      referencePulse k t := by
  change toProjectiveState (normalizedMaxCurve (referenceEntryState k) 0 (referenceClock k t)) = _
  rw [(referenceClock_normalized_orbit k t).2]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (referencePulse_denom_pos k t))

private theorem BianchiIX.referenceClock_chart_pos (k t : ℝ) :
    0 < 1 + normalizedMaxCurve (referenceEntryState k) 0 (referenceClock k t) 0 := by
  rw [(referenceClock_normalized_orbit k t).2]
  exact fromProjectiveState_clock_pos (referencePulse_denom_pos k t)

private theorem BianchiIX.referenceActualVariation_initial (k : ℝ) (w : ProjectiveState) :
    referenceActualVariation k w (-referenceHalfTime k) = w := by
  rw [referenceActualVariation, referenceClock_entry,
    projectiveFlowDifferential_initial (referencePulse_denom_pos k _)]
  rfl

private theorem BianchiIX.hasDerivAt_referenceActualVariation (k t : ℝ) (w : ProjectiveState) :
    HasDerivAt (referenceActualVariation k w)
      (referenceVariationVelocity k t (referenceActualVariation k w t)
        (-fderiv ℝ projectiveStateDenom (referencePulse k t) (referenceActualVariation k w t) /
          projectiveStateDenom (referencePulse k t))) t := by
  have H := hasDerivAt_projectiveFlowDifferential_apply (referencePulse_denom_pos k _)
    (referenceClock_normalized_orbit k t).1 (referenceClock_chart_pos k t) w
  rw [referenceClock_projective_orbit] at H
  exact hasDerivAt_referenceOriginalVariation
    (xi := fun s => projectiveFlowDifferential (referencePulse k (-referenceHalfTime k)) 0 s w)
    (clock := referenceClock k) H (hasDerivAt_referenceClock k t)

private theorem BianchiIX.referenceActualVariation_scattering {k : ℝ} (hk : 1 < k)
    {w : ProjectiveState} (hw : w 2 = 0) :
    referenceExitProjection k (referenceActualVariation k w (referenceHalfTime k)) =
      ![-w 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * w 1,
        Real.exp (-k * Real.arcosh k) * w 1, 0, Real.exp (-4 * Real.arcosh k / k) * w 3] := by
  have H := referenceVariation_scattering (I := univ) convex_univ hk
    (fun t _ => hasDerivAt_referenceActualVariation k t w) (mem_univ _) (mem_univ _)
    (by simpa only [referenceActualVariation_initial] using hw)
  simpa only [referenceActualVariation_initial] using H

/-- The matrix now acts on the actual exit-event derivative, with no variational premise. -/
theorem solution {k : ℝ} (hk : 1 < k)
    {w : ProjectiveState} (hw : w 2 = 0) :
    fderiv ℝ toProjectiveState (referenceExitState k)
      (normalizedEventDifferential projectiveActiveWall (referenceEntryState k) 0
        (referenceNormalizedTime k)
        (fderiv ℝ fromProjectiveState (referencePulse k (-referenceHalfTime k)) w)) =
      ![-w 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * w 1,
        Real.exp (-k * Real.arcosh k) * w 1, 0, Real.exp (-4 * Real.arcosh k / k) * w 3] := by
  rw [referenceCore_event_differential hk]
  have H := referenceActualVariation_scattering hk hw
  rw [referenceActualVariation, referenceClock_exit] at H
  unfold projectiveFlowDifferential at H
  change referenceExitProjection k
    (fderiv ℝ toProjectiveState
      (normalizedMaxCurve (referenceEntryState k) 0 (referenceNormalizedTime k))
      (normalizedFlowDifferential (referenceEntryState k) 0 (referenceNormalizedTime k)
        (fderiv ℝ fromProjectiveState (referencePulse k (-referenceHalfTime k)) w))) = _ at H
  rw [(referenceEntryState_crossing hk).2] at H
  exact H
