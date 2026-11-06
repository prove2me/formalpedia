-- Prove2me | solution 1 for BianchiIX.hasDerivAt_projectiveFlowDifferential_apply
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:46:33.236563+00:00
-- url     : https://prove2.me/submissions/a41aeba1-b7c8-4c39-92f9-62873a9ce0a6

import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_projectiveOriginalField
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_contDiff_normalizedField
import Theorems.Thm_BianchiIX_continuous_projectiveStateDenom
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_coordinate_variation
import Theorems.Thm_BianchiIX_hasDerivAt_normalizedFlowDifferential
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_projective_inverse_scale
import Theorems.Thm_BianchiIX_toProjectiveState_denom_pos
import Theorems.Thm_BianchiIX_toProjectiveState_fderiv_field
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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.isOpen_normalizedFlowDomain (t₀ : ℝ) : IsOpen (normalizedFlowDomain t₀) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact mem_interior_iff_mem_nhds.mp (normalizedMaxCurve_regular hz).1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

/-- The actual initial-state derivative satisfies the reduced variational equation. -/
theorem solution {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) (w : ProjectiveState) :
    HasDerivAt (fun s => projectiveFlowDifferential y t₀ s w)
      (fderiv ℝ projectiveOriginalField (projectiveOriginalFlow y t₀ t)
        (projectiveFlowDifferential y t₀ t w)) t := by
  let alpha := normalizedMaxCurve (fromProjectiveState y) t₀
  let b : ProjectiveState → NormalizedState := fun z => normalizedMaxCurve (fromProjectiveState z) t₀ t
  let v : ℝ → NormalizedState := fun s => normalizedFlowDifferential (fromProjectiveState y) t₀ s
    (fderiv ℝ fromProjectiveState y w)
  have hfrom := ((contDiffAt_fromProjectiveState 1 (ne_of_gt hD)).differentiableAt (by norm_num)).hasFDerivAt
  have hb := (hasFDerivAt_normalizedMaxCurve_initial ht).comp y hfrom
  have hv : HasDerivAt v (fderiv ℝ normalizedField (alpha t) (v t)) t := by
    simpa only [v, alpha, normalizedDifferential, ContinuousLinearMap.comp_apply, map_zero, add_zero] using
      (hasDerivAt_normalizedFlowDifferential ht).clm_apply
        (hasDerivAt_const t (fderiv ℝ fromProjectiveState y w))
  have hc : stateConstraint (alpha t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have heq : (fun z => fderiv ℝ toProjectiveState (b z) (normalizedField (b z)))
      =ᶠ[𝓝 y] (fun z => projectiveOriginalField (toProjectiveState (b z))) := by
    have hdomain : ∀ᶠ z in 𝓝 y, t ∈ normalizedMaxDomain (fromProjectiveState z) t₀ :=
      (hfrom.continuousAt.prodMk continuousAt_const).eventually
        ((isOpen_normalizedFlowDomain t₀).mem_nhds ht)
    have hclock : ∀ᶠ z in 𝓝 y, 1 + b z 0 ≠ 0 :=
      (continuousAt_const.add ((continuous_apply 0).continuousAt.comp hb.continuousAt)).eventually_ne
        (ne_of_gt hA)
    filter_upwards [hdomain, hclock,
      continuous_projectiveStateDenom.continuousAt.eventually_ne (ne_of_gt hD)] with z hz hAz hDz
    have hcz : stateConstraint (b z) = 1 :=
      (normalizedMaxCurve_constraint hz).trans (fromProjectiveState_constraint hDz)
    rw [toProjectiveState_fderiv_field hAz hcz]
    have hs : 6 / projectiveStateDenom (toProjectiveState (b z)) = 1 + b z 0 :=
      projective_inverse_scale hAz hcz
    rw [projectiveOriginalField, hs]
  exact hasDerivAt_coordinate_variation (contDiffAt_toProjectiveState 2 (ne_of_gt hA))
    ((contDiff_normalizedField 1).differentiable (by norm_num) (alpha t))
    ((contDiffAt_projectiveOriginalField 1 (ne_of_gt (toProjectiveState_denom_pos hA hc))).differentiableAt
      (by norm_num))
    (hasDerivAt_normalizedMaxCurve ht) hv hb rfl rfl heq
