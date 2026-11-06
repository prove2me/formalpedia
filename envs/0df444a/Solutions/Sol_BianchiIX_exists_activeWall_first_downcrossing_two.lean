-- Prove2me | solution 1 for BianchiIX.exists_activeWall_first_downcrossing_two
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:29:42.470371+00:00
-- url     : https://prove2.me/submissions/39b06baa-97f8-43e9-b8d4-d7db761acc95

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_contDiffAt_scalar_event_branch
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuousAt_activeWall_event_rate
import Theorems.Thm_BianchiIX_eventually_activeWall_first_downcrossing
import Theorems.Thm_BianchiIX_exists_normalized_event
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
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_scalar_event_branch_two {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Q : E × ℝ → ℝ} {x : E} {t a : ℝ}
    (hQ : ContDiffAt ℝ 2 Q (x, t))
    (hd : HasDerivAt (fun u => Q (x, u)) a t) (ha : a ≠ 0)
    {τ : E → ℝ} (hτ : τ x = t) (hcτ : ContinuousAt τ x)
    (hhit : ∀ᶠ y in 𝓝 x, Q (y, τ y) = Q (x, t)) : ContDiffAt ℝ 2 τ x :=
  contDiffAt_scalar_event_branch (by norm_num) hQ hd ha hτ hcτ hhit

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology ContDiff

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_smooth {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ ∞ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  contDiffAt_infty.mpr (fun n => contDiffAt_normalizedMaxCurve_nat n ht)

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_two {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  (contDiffAt_normalizedMaxCurve_smooth ht).of_le (by decide)

end
end


/-- A transverse outgoing event has an ambient C2 first-downcrossing branch despite earlier upward hits. -/
theorem solution {x : NormalizedState} {t₀ s t η : ℝ}
    (hst : s < t)
    (hreg : ∀ u ∈ Icc s t, u ∈ normalizedMaxDomain x t₀ ∧ 0 < 1 + normalizedMaxCurve x t₀ u 0)
    (hbefore : ∀ u ∈ Ico s t,
      projectiveActiveWall (normalizedMaxCurve x t₀ u) ≠ η ∨
        0 < normalizedEventRate projectiveActiveWall x t₀ u)
    (hrate : normalizedEventRate projectiveActiveWall x t₀ t < 0)
    (hhit : projectiveActiveWall (normalizedMaxCurve x t₀ t) = η) :
    ∃ τ : NormalizedState → ℝ, τ x = t ∧ ContDiffAt ℝ 2 τ x ∧
      ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y))) x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x t₀ t) x ∧
      HasFDerivAt (fun y => toProjectiveState (normalizedMaxCurve y t₀ (τ y)))
        ((fderiv ℝ toProjectiveState (normalizedMaxCurve x t₀ t)).comp
          (normalizedEventDifferential projectiveActiveWall x t₀ t)) x ∧
      (∀ᶠ y in 𝓝 x,
        IsLeast {u | s < u ∧ u ∈ normalizedMaxDomain y t₀ ∧
          projectiveActiveWall (normalizedMaxCurve y t₀ u) = η ∧
          normalizedEventRate projectiveActiveWall y t₀ u < 0} (τ y) ∧
        (∀ u ∈ Icc s (τ y), u ∈ normalizedMaxDomain y t₀ ∧ 0 < 1 + normalizedMaxCurve y t₀ u 0)) := by
  have hdom := (hreg t ⟨hst.le, le_rfl⟩).1
  have hA := ne_of_gt (hreg t ⟨hst.le, le_rfl⟩).2
  have hg := contDiffAt_projectiveActiveWall 2 hA
  obtain ⟨τ, hτ, hcτ, hdτ, hlocal, huniq, _, hdEnd⟩ := exists_normalized_event hdom
    (contDiffAt_projectiveActiveWall 1 hA) (ne_of_lt hrate)
  let F : NormalizedState × ℝ → NormalizedState := fun z => normalizedMaxCurve z.1 t₀ z.2
  let Q : NormalizedState × ℝ → ℝ := fun z => projectiveActiveWall (F z)
  have hcF : ContDiffAt ℝ 2 F (x, t) := contDiffAt_normalizedMaxCurve_two hdom
  have hcQ : ContDiffAt ℝ 2 Q (x, t) :=
    ContDiffAt.comp (g := projectiveActiveWall) (f := F) (x, t) hg hcF
  have htime : HasDerivAt (fun u => Q (x, u)) (normalizedEventRate projectiveActiveWall x t₀ t) t :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_normalizedMaxCurve hdom)
  have hτ2 := contDiffAt_scalar_event_branch_two hcQ htime (ne_of_lt hrate) hτ
    hcτ.continuousAt (hlocal.mono fun _ h => h.2)
  have hcEnd : ContDiffAt ℝ 2 (fun y => F (y, τ y)) x := by
    have H : ContDiffAt ℝ 2 F (x, τ x) := by rw [hτ]; exact hcF
    exact H.comp x (contDiffAt_id.prodMk hτ2)
  have hto : ContDiffAt ℝ 2 toProjectiveState (F (x, τ x)) := by
    rw [hτ]
    exact contDiffAt_toProjectiveState 2 hA
  have hdOut := (hto.differentiableAt (by norm_num)).hasFDerivAt.comp x hdEnd
  rw [hτ] at hdOut
  have hgraph : Tendsto (fun y => (y, τ y)) (𝓝 x) (𝓝 (x, t)) := by
    simpa only [hτ, id_eq] using (continuousAt_id.prodMk hcτ.continuousAt).tendsto
  have Hrate := hgraph.eventually ((continuousAt_activeWall_event_rate hdom hA).eventually
    (isOpen_Iio.mem_nhds hrate))
  refine ⟨τ, hτ, hτ2,
    ContDiffAt.comp (g := toProjectiveState) (f := fun y => F (y, τ y)) x hto hcEnd, hdτ, hdOut, ?_⟩
  apply eventually_activeWall_first_downcrossing hcτ.continuousAt
    (by rw [hτ]; exact hst) (by simpa only [hτ] using hreg) (by simpa only [hτ] using hbefore)
    ((hlocal.mono fun _ h => h.2.trans hhit).and Hrate)
  rw [hτ]
  exact huniq.mono fun _ h hh => h.2.mp (hh.trans hhit.symm)
