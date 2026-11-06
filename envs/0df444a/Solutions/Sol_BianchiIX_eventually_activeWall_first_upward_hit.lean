-- Prove2me | solution 1 for BianchiIX.eventually_activeWall_first_upward_hit
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T07:07:56.352026+00:00
-- url     : https://prove2.me/submissions/bcc9de86-0bb0-4c2d-9aea-1520a48dd55d

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_continuousAt_activeWall_event_rate
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

theorem solution {x : NormalizedState} {τ : NormalizedState → ℝ} {η : ℝ}
    (hcτ : ContinuousAt τ x) (hT : 0 < τ x)
    (hreg : ∀ t ∈ Icc 0 (τ x), t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0)
    (hrate : ∀ t ∈ Icc 0 (τ x), 0 < normalizedEventRate projectiveActiveWall x 0 t)
    (hhit : ∀ᶠ y in 𝓝 x, projectiveActiveWall (normalizedMaxCurve y 0 (τ y)) = η) :
    ∀ᶠ y in 𝓝 x,
      IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain y 0 ∧ projectiveActiveWall (normalizedMaxCurve y 0 t) = η} (τ y) ∧
      (∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 t 0) ∧
      (∀ t ∈ Ico 0 (τ y), projectiveActiveWall (normalizedMaxCurve y 0 t) < η) ∧
      (∀ t ∈ Icc 0 (τ y), 0 < normalizedEventRate projectiveActiveWall y 0 t) := by
  have hpersist : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc 0 (τ y),
      t ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 t 0 ∧
        0 < normalizedEventRate projectiveActiveWall y 0 t := by
    apply eventually_forall_movingInterval hcτ hT
    intro t ht
    have hflow := (normalizedMaxCurve_regular (hreg t ht).1).2.continuousAt
    have hA : ContinuousAt (fun z : NormalizedState × ℝ => 1 + normalizedMaxCurve z.1 0 z.2 0) (x, t) :=
      continuousAt_const.add (continuousAt_pi.mp hflow 0)
    have hdom : ∀ᶠ z : NormalizedState × ℝ in 𝓝 (x, t), z.2 ∈ normalizedMaxDomain z.1 0 :=
      (isOpen_normalizedFlowDomain 0).mem_nhds (hreg t ht).1
    exact hdom.and
      ((hA.eventually (isOpen_Ioi.mem_nhds (hreg t ht).2)).and
        ((continuousAt_activeWall_event_rate (hreg t ht).1 (hreg t ht).2.ne').eventually
          (isOpen_Ioi.mem_nhds (hrate t ht))))
  have hpos := hcτ.eventually (isOpen_Ioi.mem_nhds hT)
  filter_upwards [hpersist, hpos, hhit] with y hy hτ hhit_y
  have htmem : τ y ∈ Icc 0 (τ y) := ⟨hτ.le, le_rfl⟩
  have hd (t : ℝ) (ht : t ∈ Icc 0 (τ y)) :
      HasDerivAt (fun s => projectiveActiveWall (normalizedMaxCurve y 0 s))
        (normalizedEventRate projectiveActiveWall y 0 t) t := by
    exact ((contDiffAt_projectiveActiveWall 1 (hy t ht).2.1.ne').differentiableAt
      (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_normalizedMaxCurve (hy t ht).1)
  have hmono : StrictMonoOn (fun t => projectiveActiveWall (normalizedMaxCurve y 0 t)) (Icc 0 (τ y)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (HasDerivAt.continuousOn hd)
    intro t ht
    rw [(hd t (interior_subset ht)).deriv]
    exact (hy t (interior_subset ht)).2.2
  have hbefore (t : ℝ) (ht : t ∈ Ico 0 (τ y)) : projectiveActiveWall (normalizedMaxCurve y 0 t) < η := by
    simpa only [hhit_y] using hmono ⟨ht.1, ht.2.le⟩ htmem ht.2
  refine ⟨⟨⟨hτ, (hy _ htmem).1, hhit_y⟩, ?_⟩,
    (fun t ht => ⟨(hy t ht).1, (hy t ht).2.1⟩), hbefore, fun t ht => (hy t ht).2.2⟩
  intro t ht
  by_contra hnot
  have H := hbefore t ⟨ht.1.le, lt_of_not_ge hnot⟩
  rw [ht.2.2] at H
  exact lt_irrefl _ H
