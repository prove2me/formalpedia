-- Prove2me | solution 1 for BianchiIX.exists_normalized_event
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:28:42.844399+00:00
-- url     : https://prove2.me/submissions/c066a5f3-cd5a-42b2-bfd3-227f35cbd688

import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
import Theorems.Thm_BianchiIX_hasFDerivAt_normalizedMaxCurve
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
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

noncomputable section
open BianchiIX
open Set Filter Metric
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

private theorem BianchiIX.scalar_map_inverse {a : ℝ} (ha : a ≠ 0) :
    (a • ContinuousLinearMap.id ℝ ℝ).IsInvertible ∧
      (a • ContinuousLinearMap.id ℝ ℝ).inverse = a⁻¹ • ContinuousLinearMap.id ℝ ℝ := by
  have hright : (a • ContinuousLinearMap.id ℝ ℝ).comp (a⁻¹ • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [ha]
  have hleft : (a⁻¹ • ContinuousLinearMap.id ℝ ℝ).comp (a • ContinuousLinearMap.id ℝ ℝ) =
      ContinuousLinearMap.id ℝ ℝ := by ext; simp [ha]
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hright hleft,
    ContinuousLinearMap.inverse_eq hright hleft⟩

/-- A transverse crossing defines a locally unique smooth event time and endpoint map. -/
theorem solution {x : NormalizedState} {t₀ t : ℝ} {g : NormalizedState → ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀)
    (hg : ContDiffAt ℝ 1 g (normalizedMaxCurve x t₀ t))
    (htrans : normalizedEventRate g x t₀ t ≠ 0) :
    ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 1 τ x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential g x t₀ t) x ∧
      (∀ᶠ y in 𝓝 x, τ y ∈ normalizedMaxDomain y t₀ ∧
        g (normalizedMaxCurve y t₀ (τ y)) = g (normalizedMaxCurve x t₀ t)) ∧
      (∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 t₀ ∧
        (g (normalizedMaxCurve z.1 t₀ z.2) = g (normalizedMaxCurve x t₀ t) ↔ τ z.1 = z.2)) ∧
      ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y t₀ (τ y)) x ∧
      HasFDerivAt (fun y => normalizedMaxCurve y t₀ (τ y)) (normalizedEventDifferential g x t₀ t) x := by
  let Q : NormalizedState × ℝ → ℝ := fun z => g (normalizedMaxCurve z.1 t₀ z.2)
  have hcQ : ContDiffAt ℝ 1 Q (x, t) := hg.comp (x, t) (normalizedMaxCurve_regular ht).2
  have hdQ := (hg.differentiableAt (by norm_num)).hasFDerivAt.comp (x, t)
    (hasFDerivAt_normalizedMaxCurve ht)
  have htime : (fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ NormalizedState ℝ) =
      normalizedEventRate g x t₀ t • ContinuousLinearMap.id ℝ ℝ := by
    rw [show fderiv ℝ Q (x, t) = _ from hdQ.fderiv]
    ext
    simp [normalizedEventRate, ContinuousLinearMap.comp_apply, mul_comm]
  have hinitial : (fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inl ℝ NormalizedState ℝ) =
      (fderiv ℝ g (normalizedMaxCurve x t₀ t)).comp (normalizedFlowDifferential x t₀ t) := by
    rw [show fderiv ℝ Q (x, t) = _ from hdQ.fderiv]
    simp [ContinuousLinearMap.comp_assoc]
  have hinv : ((fderiv ℝ Q (x, t)).comp (ContinuousLinearMap.inr ℝ NormalizedState ℝ)).IsInvertible := by
    rw [htime]
    exact (scalar_map_inverse htrans).1
  let τ := hcQ.implicitFunction (by norm_num) hinv
  have hτinit : τ x = t := hcQ.implicitFunction_apply_self (by norm_num) hinv
  have hcτ : ContDiffAt ℝ 1 τ x := hcQ.contDiffAt_implicitFunction (by norm_num) hinv
  have hdτ : HasFDerivAt τ (normalizedEventTimeDifferential g x t₀ t) x := by
    have H := (hcQ.hasStrictFDerivAt_implicitFunction (by norm_num) hinv).hasFDerivAt
    rw [htime, hinitial, (scalar_map_inverse htrans).2] at H
    convert! H using 1
    ext v
    simp [normalizedEventTimeDifferential]
  have hgraph : Tendsto (fun y => (y, τ y)) (𝓝 x) (𝓝 (x, t)) := by
    have H : ContinuousAt (fun y : NormalizedState => (y, τ y)) x := by fun_prop
    simpa only [hτinit] using H.tendsto
  have hdomain : normalizedFlowDomain t₀ ∈ 𝓝 (x, t) :=
    (isOpen_normalizedFlowDomain t₀).mem_nhds ht
  have hhit : ∀ᶠ y in 𝓝 x, τ y ∈ normalizedMaxDomain y t₀ ∧
      g (normalizedMaxCurve y t₀ (τ y)) = g (normalizedMaxCurve x t₀ t) :=
    (hgraph.eventually hdomain).and (hcQ.eventually_apply_implicitFunction (by norm_num) hinv)
  have huniq : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 t₀ ∧
      (g (normalizedMaxCurve z.1 t₀ z.2) = g (normalizedMaxCurve x t₀ t) ↔ τ z.1 = z.2) := by
    filter_upwards [hdomain, hcQ.eventually_apply_eq_iff_implicitFunction (by norm_num) hinv] with z hz hq
    exact ⟨hz, hq⟩
  have hcFlow : ContDiffAt ℝ 1
      (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, τ x) := by
    rw [hτinit]
    exact (normalizedMaxCurve_regular ht).2
  have hdFlow : HasFDerivAt (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
      ((normalizedFlowDifferential x t₀ t).coprod
        ((ContinuousLinearMap.id ℝ ℝ).smulRight (normalizedField (normalizedMaxCurve x t₀ t))))
      (x, τ x) := by
    rw [hτinit]
    exact hasFDerivAt_normalizedMaxCurve ht
  have hcMap : ContDiffAt ℝ 1 (fun y => normalizedMaxCurve y t₀ (τ y)) x := by
    convert! hcFlow.comp x (contDiffAt_id.prodMk hcτ) using 1
  refine ⟨τ, hτinit, hcτ, hdτ, hhit, huniq, hcMap, ?_⟩
  convert! hdFlow.comp x ((hasFDerivAt_id x).prodMk hdτ) using 1
