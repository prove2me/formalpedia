-- Prove2me | solution 1 for BianchiIX.coreTail_strong_variation_invariant
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:12:36.264076+00:00
-- url     : https://prove2.me/submissions/207282ed-6ac4-44ca-a14a-a49279f129c5

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceTail
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_coreTail_reference_regular
import Theorems.Thm_BianchiIX_exists_projective_normalized_reparametrization
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveFlowDifferential_apply
import Theorems.Thm_BianchiIX_hasDerivAt_referenceClockPrimitive
import Theorems.Thm_BianchiIX_hasDerivAt_referenceOriginalVariation
import Theorems.Thm_BianchiIX_hasDerivAt_referencePulse
import Theorems.Thm_BianchiIX_hasFDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_projective_chart_differential_inverse
import Theorems.Thm_BianchiIX_referencePulse_clock_integral
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_exit
import Theorems.Thm_BianchiIX_referenceVariationInvariant_constant
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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

private theorem BianchiIX.projectiveFlowDifferential_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveFlowDifferential y t₀ t₀ = ContinuousLinearMap.id ℝ ProjectiveState := by
  rw [projectiveFlowDifferential, normalizedMaxCurve_initial, normalizedFlowDifferential_initial,
    ContinuousLinearMap.id_comp, projective_chart_differential_inverse hD]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_referenceShiftClock (k s t : ℝ) :
    HasDerivAt (referenceShiftClock k s) (projectiveStateDenom (referencePulse k t) / 6) t :=
  (hasDerivAt_referenceClockPrimitive k t).sub_const _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceShiftClock_initial (k s : ℝ) : referenceShiftClock k s s = 0 := sub_self _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceShiftClock_normalized_orbit (k s t : ℝ) :
    referenceShiftClock k s t ∈ normalizedMaxDomain (fromProjectiveState (referencePulse k s)) 0 ∧
      normalizedMaxCurve (fromProjectiveState (referencePulse k s)) 0 (referenceShiftClock k s t) =
        fromProjectiveState (referencePulse k t) := by
  obtain ⟨e, hsrc, he, _, _, _, _, _, hdom, hflow⟩ :=
    exists_projective_normalized_reparametrization (β := referencePulse k)
      (s := s) convex_univ isOpen_univ (mem_univ _)
      (fun u _ => hasDerivAt_referencePulse k u) (fun u _ => referencePulse_denom_pos k u)
  have hmem : t ∈ e.source := by rw [hsrc]; trivial
  have ht : e t = referenceShiftClock k s t := by rw [he, referencePulse_clock_integral]; rfl
  have htarget : referenceShiftClock k s t ∈ e.target := ht ▸ e.map_source hmem
  have hinv : e.symm (referenceShiftClock k s t) = t := by rw [← ht, e.left_inv hmem]
  refine ⟨hdom htarget, ?_⟩
  have H := (hflow _ htarget).1
  rw [hinv] at H
  exact H.symm

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceShiftClock_projective_orbit (k s t : ℝ) :
    projectiveOriginalFlow (referencePulse k s) 0 (referenceShiftClock k s t) = referencePulse k t := by
  unfold projectiveOriginalFlow
  rw [(referenceShiftClock_normalized_orbit k s t).2]
  exact toProjectiveState_fromProjectiveState (referencePulse_denom_pos k t).ne'

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceShiftClock_chart_pos (k s t : ℝ) :
    0 < 1 + normalizedMaxCurve (fromProjectiveState (referencePulse k s)) 0
      (referenceShiftClock k s t) 0 := by
  rw [(referenceShiftClock_normalized_orbit k s t).2]
  exact fromProjectiveState_clock_pos (referencePulse_denom_pos k t)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceShiftedVariation_initial (k s : ℝ) (w : ProjectiveState) :
    referenceShiftedVariation k s w s = w := by
  rw [referenceShiftedVariation, referenceShiftClock_initial,
    projectiveFlowDifferential_initial (referencePulse_denom_pos k s)]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_referenceShiftedVariation (k s t : ℝ) (w : ProjectiveState) :
    HasDerivAt (referenceShiftedVariation k s w)
      (referenceVariationVelocity k t (referenceShiftedVariation k s w t)
        (-fderiv ℝ projectiveStateDenom (referencePulse k t) (referenceShiftedVariation k s w t) /
          projectiveStateDenom (referencePulse k t))) t := by
  have H := hasDerivAt_projectiveFlowDifferential_apply (referencePulse_denom_pos k s)
    (referenceShiftClock_normalized_orbit k s t).1 (referenceShiftClock_chart_pos k s t) w
  rw [referenceShiftClock_projective_orbit] at H
  exact hasDerivAt_referenceOriginalVariation
    (xi := fun r => projectiveFlowDifferential (referencePulse k s) 0 r w)
    (clock := referenceShiftClock k s) H (hasDerivAt_referenceShiftClock k s t)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreTailEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreTailEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreTailEntry] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreTailEntry_reference {k : ℝ} (hk : 1 < k) :
    coreTailEntry ![k, 0, 0] = referencePulse k (referenceHalfTime k) := by
  rw [referencePulse_exit hk]
  rfl

end
end

private theorem BianchiIX.coreTailEntry_strong_fderiv {k : ℝ} (hk : 1 < k) :
    fderiv ℝ coreTailEntry ![k, 0, 0] (Pi.single 1 1) = Pi.single 1 1 := by
  have hline : HasDerivAt (fun a : ℝ => (![k, a, 0] : CoreAngleState)) (Pi.single 1 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using hasDerivAt_const (0 : ℝ) k
    · change HasDerivAt (fun a : ℝ => a) 1 0
      exact hasDerivAt_id' 0
    · simpa using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have hentry : HasDerivAt (fun a : ℝ => coreTailEntry ![k, a, 0]) (Pi.single 1 1) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [coreTailEntry] using hasDerivAt_const (0 : ℝ) (1 - Real.sqrt (k ^ 2 - 1))
    · change HasDerivAt (fun a : ℝ => a) 1 0
      exact hasDerivAt_id' 0
    · simpa [coreTailEntry] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
    · simpa [coreTailEntry] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  exact (((contDiffAt_coreTailEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt 0 hline).unique hentry

/-- The endpoint correction is tangent to the reference orbit and drops out of the energy first integral. -/
theorem solution {k η : ℝ} (hk : 1 < k) (hη : 0 < η ∧ η < 1) :
    let z := coreTailState η ![k, 0, 0]
    let v := fderiv ℝ (coreTailState η) ![k, 0, 0] (Pi.single 1 1)
    (z 0 - 1) * v 0 + z 2 * v 2 - 2 * z 2 * v 1 = -2 := by
  let Y : CoreAngleState := ![k, 0, 0]
  let s := referenceHalfTime k
  let t := referenceHeightTime k η
  let z := referencePulse k t
  let w : ProjectiveState := Pi.single 1 1
  let ξ := referenceShiftedVariation k s w t
  let a := fderiv ℝ (coreTailTime η) Y (Pi.single 1 1)
  have H := coreTail_reference_regular hk hη
  have hc : coreTailEntry Y = referencePulse k s := coreTailEntry_reference hk
  have hT : coreTailTime η Y = referenceShiftClock k s t := by
    rw [H.1]
    exact referencePulse_clock_integral k s t
  have hz : coreTailState η Y = z := by
    unfold coreTailState
    rw [hc, hT, referenceShiftClock_projective_orbit]
  have hD : 0 < projectiveStateDenom (coreTailEntry Y) := hc ▸ referencePulse_denom_pos k s
  have hdom : coreTailTime η Y ∈ normalizedMaxDomain (fromProjectiveState (coreTailEntry Y)) 0 := by
    rw [hc, hT]
    exact (referenceShiftClock_normalized_orbit k s t).1
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState (coreTailEntry Y)) 0 (coreTailTime η Y) 0 := by
    rw [hc, hT]
    exact referenceShiftClock_chart_pos k s t
  have hmap := (((contDiffAt_coreTailEntry 1 hk).differentiableAt (by norm_num)).hasFDerivAt).prodMk
    ((H.2.2.1.differentiableAt (by norm_num)).hasFDerivAt)
  have hflow := (hasFDerivAt_projectiveOriginalFlow hD hdom hA).comp Y hmap
  change HasFDerivAt (coreTailState η) _ Y at hflow
  have hv : fderiv ℝ (coreTailState η) Y (Pi.single 1 1) = ξ + a • projectiveOriginalField z := by
    rw [hflow.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coprod_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      coreTailEntry_strong_fderiv hk]
    change projectiveFlowDifferential (coreTailEntry Y) 0 (coreTailTime η Y) w +
      a • projectiveOriginalField (coreTailState η Y) = _
    rw [hc, hT, hz]
    rfl
  have HI := referenceVariationInvariant_constant (I := univ) convex_univ
    (fun r _ => hasDerivAt_referenceShiftedVariation k s r w) (mem_univ s) (mem_univ t)
  rw [referenceShiftedVariation_initial] at HI
  dsimp only [referenceVariationInvariant] at HI
  rw [show referencePulse k s = ![1 - Real.sqrt (k ^ 2 - 1), 0, 1, 0] from referencePulse_exit hk] at HI
  change 2 * (z 0 - 1) * ξ 0 + 2 * z 2 * ξ 2 - 4 * z 2 * ξ 1 =
    2 * ((1 - Real.sqrt (k ^ 2 - 1)) - 1) * w 0 + 2 * 1 * w 2 - 4 * 1 * w 1 at HI
  norm_num [w, Pi.single_apply, show (2 : Fin 4) ≠ 1 by decide] at HI
  have HF : (z 0 - 1) * projectiveOriginalField z 0 + z 2 * projectiveOriginalField z 2 -
      2 * z 2 * projectiveOriginalField z 1 = 0 := by
    dsimp [z, referencePulse, projectiveOriginalField, projectiveField,
      phaseVelocity, activeVelocity, strongVelocity, coupling]
    ring
  change (coreTailState η Y 0 - 1) * fderiv ℝ (coreTailState η) Y (Pi.single 1 1) 0 +
    coreTailState η Y 2 * fderiv ℝ (coreTailState η) Y (Pi.single 1 1) 2 -
      2 * coreTailState η Y 2 * fderiv ℝ (coreTailState η) Y (Pi.single 1 1) 1 = -2
  rw [hz, hv]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination HI / 2 + a * HF
