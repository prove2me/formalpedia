-- Prove2me | solution 1 for BianchiIX.eventually_activeWall_interior_first_hit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:06:42.823896+00:00
-- url     : https://prove2.me/submissions/7b68a337-b370-4870-ad90-9dd05229ba8b

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_eventually_forall_movingInterval
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

/-- Interior avoidance and local uniqueness at the terminal event preserve the first hit. -/
theorem solution {x : NormalizedState}
    {τ : NormalizedState → ℝ} {t₀ s η : ℝ}
    (hcτ : ContinuousAt τ x) (hst : s < τ x)
    (hreg : ∀ t ∈ Icc s (τ x), t ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (havoid : ∀ t ∈ Ico s (τ x), projectiveActiveWall (normalizedMaxCurve x t₀ t) ≠ η)
    (hhit : ∀ᶠ y in 𝓝 x, projectiveActiveWall (normalizedMaxCurve y t₀ (τ y)) = η)
    (huniq : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, τ x),
      projectiveActiveWall (normalizedMaxCurve z.1 t₀ z.2) = η → τ z.1 = z.2) :
    ∀ᶠ y in 𝓝 x,
      IsLeast {t | s < t ∧ t ∈ normalizedMaxDomain y t₀ ∧
        projectiveActiveWall (normalizedMaxCurve y t₀ t) = η} (τ y) ∧
      (∀ t ∈ Icc s (τ y), t ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ t 0) := by
  have H : ∀ᶠ y in 𝓝 x, ∀ u ∈ Icc 0 (τ y - s),
      s + u ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ (s + u) 0 ∧
      (projectiveActiveWall (normalizedMaxCurve y t₀ (s + u)) = η → s + u = τ y) := by
    apply eventually_forall_movingInterval (hcτ.sub continuousAt_const) (sub_pos.mpr hst)
    intro u hu
    change u ∈ Icc 0 (τ x - s) at hu
    have hv : s + u ∈ Icc s (τ x) := ⟨by linarith only [hu.1], by linarith only [hu.2]⟩
    have hflow := (normalizedMaxCurve_regular (hreg _ hv).1).2.continuousAt
    have hAc : ContinuousAt (fun z : NormalizedState × ℝ => 1 + normalizedMaxCurve z.1 t₀ z.2 0) (x, s + u) :=
      continuousAt_const.add (continuousAt_pi.mp hflow 0)
    have hgc : ContinuousAt (fun z : NormalizedState × ℝ =>
        projectiveActiveWall (normalizedMaxCurve z.1 t₀ z.2)) (x, s + u) :=
      ContinuousAt.comp (g := projectiveActiveWall)
        (f := fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2)
        (contDiffAt_projectiveActiveWall 1 (ne_of_gt (hreg _ hv).2)).continuousAt hflow
    have hlocal : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, s + u),
        projectiveActiveWall (normalizedMaxCurve z.1 t₀ z.2) = η → z.2 = τ z.1 := by
      by_cases heq : s + u = τ x
      · rw [heq]
        exact huniq.mono fun _ h hhit => (h hhit).symm
      · exact (hgc.eventually_ne (havoid _ ⟨hv.1, lt_of_le_of_ne hv.2 heq⟩)).mono
          fun _ h hhit => (h hhit).elim
    have hdom : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, s + u), z.2 ∈ normalizedMaxDomain z.1 t₀ :=
      (isOpen_normalizedFlowDomain t₀).mem_nhds (hreg _ hv).1
    have hshift : ContinuousAt (fun z : NormalizedState × ℝ => (z.1, s + z.2)) (x, u) :=
      continuousAt_fst.prodMk (continuousAt_const.add continuousAt_snd)
    exact hshift.eventually (hdom.and ((hAc.eventually (isOpen_Ioi.mem_nhds (hreg _ hv).2)).and hlocal))
  filter_upwards [H, hcτ.eventually (isOpen_Ioi.mem_nhds hst), hhit] with y hy hsy hhit_y
  have Ht (t : ℝ) (ht : t ∈ Icc s (τ y)) :
      t ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ t 0 ∧
      (projectiveActiveWall (normalizedMaxCurve y t₀ t) = η → t = τ y) := by
    simpa only [add_sub_cancel] using hy (t - s)
      ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 s⟩
  refine ⟨⟨⟨hsy, (Ht _ ⟨hsy.le, le_rfl⟩).1, hhit_y⟩, ?_⟩,
    fun t ht => ⟨(Ht t ht).1, (Ht t ht).2.1⟩⟩
  intro t ht
  by_contra! hlt
  exact (ne_of_lt hlt) ((Ht t ⟨ht.1.le, hlt.le⟩).2.2 ht.2.2)
