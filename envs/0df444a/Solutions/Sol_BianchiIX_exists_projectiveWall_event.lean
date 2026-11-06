-- Prove2me | solution 1 for BianchiIX.exists_projectiveWall_event
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:03:18.454647+00:00
-- url     : https://prove2.me/submissions/97252bcd-1dc6-415a-8436-9d28500897f5

import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreExitEvents
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv_field
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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

/-- The constant active-wall event, in projective initial coordinates, uses the actual flow. -/
theorem solution {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0)
    (hv : projectiveField (projectiveOriginalFlow y t₀ t) 2 ≠ 0) :
    ∃ τ : ProjectiveState → ℝ, τ y = t ∧ ContDiffAt ℝ 1 τ y ∧
      (∀ᶠ z in 𝓝 y, τ z ∈ normalizedMaxDomain (fromProjectiveState z) t₀ ∧
        0 < 1 + normalizedMaxCurve (fromProjectiveState z) t₀ (τ z) 0 ∧
        projectiveOriginalFlow z t₀ (τ z) 2 = projectiveOriginalFlow y t₀ t 2) ∧
      (∀ᶠ z : ProjectiveState × ℝ in 𝓝 (y, t),
        z.2 ∈ normalizedMaxDomain (fromProjectiveState z.1) t₀ ∧
        (projectiveOriginalFlow z.1 t₀ z.2 2 = projectiveOriginalFlow y t₀ t 2 ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun z => projectiveOriginalFlow z t₀ (τ z)) y ∧
      HasFDerivAt (fun z => projectiveOriginalFlow z t₀ (τ z))
        (projectiveWallArrivalDifferential y t₀ t) y := by
  let x := fromProjectiveState y
  let X := normalizedMaxCurve x t₀ t
  have hc : stateConstraint X = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  have htrans : normalizedEventRate projectiveActiveWall x t₀ t ≠ 0 := by
    change fderiv ℝ projectiveActiveWall X (normalizedField X) ≠ 0
    rw [projectiveActiveWall_fderiv_field (ne_of_gt hA) hc]
    exact mul_ne_zero (ne_of_gt hA) hv
  obtain ⟨tau, hinit, hctau, _, hhit, huniq, hcmap, hdmap⟩ :=
    exists_normalized_event ht (contDiffAt_projectiveActiveWall 1 (ne_of_gt hA)) htrans
  let τ : ProjectiveState → ℝ := fun z => tau (fromProjectiveState z)
  have hfrom := contDiffAt_fromProjectiveState 1 (ne_of_gt hD)
  have hfrom' := (hfrom.differentiableAt (by norm_num)).hasFDerivAt
  have hτ : τ y = t := hinit
  let eta : ProjectiveState → NormalizedState := fun z => normalizedMaxCurve (fromProjectiveState z) t₀ (τ z)
  have hceta : ContDiffAt ℝ 1 eta y := hcmap.comp y hfrom
  have heta : eta y = X := by change normalizedMaxCurve x t₀ (τ y) = X; rw [hτ]
  have hto : ContDiffAt ℝ 1 toProjectiveState (eta y) := by
    rw [heta]
    exact contDiffAt_toProjectiveState 1 (ne_of_gt hA)
  have hAnear : ∀ᶠ z in 𝓝 y, 0 < 1 + eta z 0 := by
    have H : ContinuousAt (fun z => 1 + eta z 0) y :=
      continuousAt_const.add ((continuous_apply 0).continuousAt.comp hceta.continuousAt)
    apply H.eventually (isOpen_Ioi.mem_nhds ?_)
    change 0 < 1 + eta y 0
    rw [heta]
    exact hA
  refine ⟨τ, hτ, hctau.comp y hfrom, ?_, ?_, hto.comp y hceta, ?_⟩
  · filter_upwards [hfrom.continuousAt.eventually hhit, hAnear] with z hz hAz
    exact ⟨hz.1, hAz, hz.2⟩
  · have hfamily : ContinuousAt (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2))
        (y, t) := by
      convert! (hfrom.continuousAt.comp
        (continuousAt_fst : ContinuousAt (Prod.fst : ProjectiveState × ℝ → ProjectiveState) (y, t))).prodMk
          continuousAt_snd using 1
    exact hfamily.eventually huniq
  · have H := ((hto.differentiableAt (by norm_num)).hasFDerivAt).comp y (hdmap.comp y hfrom')
    rw [heta] at H
    convert! H using 1
