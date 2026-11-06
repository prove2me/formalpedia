-- Prove2me | solution 1 for BianchiIX.exists_activeWall_first_downward_hit_two
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T04:51:01.702782+00:00
-- url     : https://prove2.me/submissions/933e5c9f-ac59-40e0-8490-336127dd4725

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Events
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_contDiffAt_scalar_event_branch
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_eventually_activeWall_first_downward_hit
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

theorem solution {x : NormalizedState} {T η : ℝ} (hT : 0 < T)
    (hreg : ∀ t ∈ Icc 0 T, t ∈ normalizedMaxDomain x 0 ∧ 0 < 1 + normalizedMaxCurve x 0 t 0)
    (hrate : ∀ t ∈ Icc 0 T, normalizedEventRate projectiveActiveWall x 0 t < 0)
    (hhit : projectiveActiveWall (normalizedMaxCurve x 0 T) = η) :
    ∃ τ : NormalizedState → ℝ, τ x = T ∧ ContDiffAt ℝ 2 τ x ∧
      ContDiffAt ℝ 2 (fun y => toProjectiveState (normalizedMaxCurve y 0 (τ y))) x ∧
      HasFDerivAt τ (normalizedEventTimeDifferential projectiveActiveWall x 0 T) x ∧
      (∀ᶠ y in 𝓝 x,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain y 0 ∧ projectiveActiveWall (normalizedMaxCurve y 0 t) = η} (τ y) ∧
        (∀ t ∈ Icc 0 (τ y), t ∈ normalizedMaxDomain y 0 ∧ 0 < 1 + normalizedMaxCurve y 0 t 0) ∧
        (∀ t ∈ Ico 0 (τ y), η < projectiveActiveWall (normalizedMaxCurve y 0 t)) ∧
        (∀ t ∈ Icc 0 (τ y), normalizedEventRate projectiveActiveWall y 0 t < 0)) := by
  have htmem : T ∈ Icc 0 T := ⟨hT.le, le_rfl⟩
  have hdom := (hreg T htmem).1
  have hA := ne_of_gt (hreg T htmem).2
  have hg := contDiffAt_projectiveActiveWall 2 hA
  obtain ⟨τ, hτ, hcτ, hdτ, hlocal, _, _, _⟩ := exists_normalized_event hdom
    (contDiffAt_projectiveActiveWall 1 hA) (ne_of_lt (hrate T htmem))
  let F : NormalizedState × ℝ → NormalizedState := fun z => normalizedMaxCurve z.1 0 z.2
  let Q : NormalizedState × ℝ → ℝ := fun z => projectiveActiveWall (F z)
  have hcF : ContDiffAt ℝ 2 F (x, T) := contDiffAt_normalizedMaxCurve_two hdom
  have hcQ : ContDiffAt ℝ 2 Q (x, T) :=
    ContDiffAt.comp (g := projectiveActiveWall) (f := F) (x, T) hg hcF
  have htime : HasDerivAt (fun s => Q (x, s)) (normalizedEventRate projectiveActiveWall x 0 T) T :=
    (hg.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt T (hasDerivAt_normalizedMaxCurve hdom)
  have hτ2 := contDiffAt_scalar_event_branch_two hcQ htime (ne_of_lt (hrate T htmem)) hτ
    hcτ.continuousAt (hlocal.mono fun _ h => h.2)
  have hcEnd : ContDiffAt ℝ 2 (fun y => F (y, τ y)) x := by
    have H : ContDiffAt ℝ 2 F (x, τ x) := by rw [hτ]; exact hcF
    exact H.comp x (contDiffAt_id.prodMk hτ2)
  have hto : ContDiffAt ℝ 2 toProjectiveState (F (x, τ x)) := by
    rw [hτ]
    exact contDiffAt_toProjectiveState 2 hA
  have hcOut : ContDiffAt ℝ 2 (fun y => toProjectiveState (F (y, τ y))) x :=
    ContDiffAt.comp (g := toProjectiveState) (f := fun y => F (y, τ y)) x hto hcEnd
  refine ⟨τ, hτ, hτ2, hcOut, hdτ, ?_⟩
  apply eventually_activeWall_first_downward_hit hcτ.continuousAt
    (by rw [hτ]; exact hT) (by simpa only [hτ] using hreg) (by simpa only [hτ] using hrate)
  exact hlocal.mono fun _ h => h.2.trans hhit
