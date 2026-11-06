-- Prove2me | solution 1 for BianchiIX.exists_referenceCore_firstReturn_two
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:13:54.743434+00:00
-- url     : https://prove2.me/submissions/8333fd8f-c9f4-4666-8758-63425f1960b6

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_contDiffAt_scalar_event_branch
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_referenceCore_firstReturn
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
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
open Set Filter
open scoped Topology

private theorem BianchiIX.referenceExitState_clock_pos (k : ℝ) : 0 < 1 + referenceExitState k 0 :=
  fromProjectiveState_clock_pos (referencePulse_denom_pos k _)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.referenceExitState_constraint (k : ℝ) : stateConstraint (referenceExitState k) = 1 :=
  fromProjectiveState_constraint (ne_of_gt (referencePulse_denom_pos k _))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.referenceExitState_projective (k : ℝ) :
    toProjectiveState (referenceExitState k) = referencePulse k (referenceHalfTime k) :=
  toProjectiveState_fromProjectiveState (ne_of_gt (referencePulse_denom_pos k _))

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

private theorem BianchiIX.referenceExitState_rate_neg {k : ℝ} (hk : 1 < k) :
    fderiv ℝ projectiveActiveWall (referenceExitState k) (normalizedField (referenceExitState k)) < 0 := by
  rw [projectiveActiveWall_fderiv_field (ne_of_gt (referenceExitState_clock_pos k))
    (referenceExitState_constraint k), referenceExitState_projective, referencePulse_exit_field hk]
  exact mul_neg_of_pos_of_neg (referenceExitState_clock_pos k) (neg_neg_of_pos (referenceCoreGap_pos hk))

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

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_coreSectionEmbedding (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionEmbedding := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionEmbedding] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiff_coreSectionCoordinates (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionCoordinates] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.referenceCoreInput_embedding {k : ℝ} (hk : 1 < k) :
    coreSectionEmbedding (referenceCoreInput k) = referencePulse k (-referenceHalfTime k) := by
  rw [referencePulse_entry hk]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.referenceCoreInput_chart {k : ℝ} (hk : 1 < k) :
    coreSectionChart (referenceCoreInput k) = referenceEntryState k := by
  rw [coreSectionChart, referenceCoreInput_embedding hk]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_referenceCoreChart {k : ℝ} (hk : 1 < k) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n coreSectionChart (referenceCoreInput k) := by
  have hf := contDiffAt_fromProjectiveState n
    (ne_of_gt (referencePulse_denom_pos k (-referenceHalfTime k)))
  rw [← referenceCoreInput_embedding hk] at hf
  exact hf.comp _ (contDiff_coreSectionEmbedding n).contDiffAt

end
end

/-- The previously identified first-return branch is twice continuously differentiable. -/
theorem solution {k : ℝ} (hk : 1 < k) :
    ∃ (τ : CoreCoordinates → ℝ) (P : CoreCoordinates → CoreCoordinates),
      τ (referenceCoreInput k) = referenceNormalizedTime k ∧
      P (referenceCoreInput k) = referenceCoreOutput k ∧
      ContDiffAt ℝ 2 τ (referenceCoreInput k) ∧ ContDiffAt ℝ 2 P (referenceCoreInput k) ∧
      (∀ᶠ z in 𝓝 (referenceCoreInput k),
        IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
          projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t) = 1} (τ z) ∧
        (∀ t ∈ Icc 0 (τ z), t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
          0 < 1 + normalizedMaxCurve (coreSectionChart z) 0 t 0) ∧
        (∀ t ∈ Ioo 0 (τ z), 1 < projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t)) ∧
        normalizedEventRate projectiveActiveWall (coreSectionChart z) 0 (τ z) < 0 ∧
        toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (τ z)) = coreSectionEmbedding (P z)) ∧
      (∀ v : CoreCoordinates, fderiv ℝ P (referenceCoreInput k) v =
        ![-v 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * v 1,
          Real.exp (-k * Real.arcosh k) * v 1, Real.exp (-4 * Real.arcosh k / k) * v 2]) := by
  obtain ⟨τ, P, hτ, hP, hcτ, _, hfirst, hdP⟩ := exists_referenceCore_firstReturn hk
  let z₀ := referenceCoreInput k
  let T := referenceNormalizedTime k
  let F : CoreCoordinates × ℝ → NormalizedState := fun z => normalizedMaxCurve (coreSectionChart z.1) 0 z.2
  let Q : CoreCoordinates × ℝ → ℝ := fun z => projectiveActiveWall (F z)
  have hcross : T ∈ normalizedMaxDomain (coreSectionChart z₀) 0 := by
    rw [referenceCoreInput_chart hk]
    exact (referenceEntryState_crossing hk).1
  have hFvalue : F (z₀, T) = referenceExitState k := by
    dsimp [F, z₀, T]
    rw [referenceCoreInput_chart hk, (referenceEntryState_crossing hk).2]
  have hcC : ContDiffAt ℝ 2 coreSectionChart z₀ := contDiffAt_referenceCoreChart hk 2
  have hcF : ContDiffAt ℝ 2 F (z₀, T) :=
    (contDiffAt_normalizedMaxCurve_two hcross).comp (z₀, T)
      ((hcC.comp (z₀, T) contDiffAt_fst).prodMk contDiffAt_snd)
  have hwall : ContDiffAt ℝ 2 projectiveActiveWall (F (z₀, T)) := by
    rw [hFvalue]
    exact contDiffAt_projectiveActiveWall 2 (ne_of_gt (referenceExitState_clock_pos k))
  have hcQ : ContDiffAt ℝ 2 Q (z₀, T) := hwall.comp (z₀, T) hcF
  have htime : HasDerivAt (fun u => Q (z₀, u))
      (normalizedEventRate projectiveActiveWall (coreSectionChart z₀) 0 T) T := by
    convert! (hwall.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt T
      (hasDerivAt_normalizedMaxCurve hcross) using 1
  have htrans : normalizedEventRate projectiveActiveWall (coreSectionChart z₀) 0 T ≠ 0 := by
    unfold normalizedEventRate
    change fderiv ℝ projectiveActiveWall (F (z₀, T)) (normalizedField (F (z₀, T))) ≠ 0
    rw [hFvalue]
    exact ne_of_lt (referenceExitState_rate_neg hk)
  have hQvalue : Q (z₀, T) = 1 := by
    have H := hfirst.self_of_nhds.1.1.2.2
    rw [hτ] at H
    exact H
  have hτ2 : ContDiffAt ℝ 2 τ z₀ := contDiffAt_scalar_event_branch_two hcQ htime htrans hτ
    hcτ.continuousAt (hfirst.mono fun _ hz => hz.1.1.2.2.trans hQvalue.symm)
  have hcEnd : ContDiffAt ℝ 2 (fun z => F (z, τ z)) z₀ := by
    have H : ContDiffAt ℝ 2 F (z₀, τ z₀) := by rw [hτ]; exact hcF
    exact H.comp z₀ (contDiffAt_id.prodMk hτ2)
  have hto : ContDiffAt ℝ 2 toProjectiveState (F (z₀, τ z₀)) := by
    rw [hτ, hFvalue]
    exact contDiffAt_toProjectiveState 2 (ne_of_gt (referenceExitState_clock_pos k))
  have hcProjective : ContDiffAt ℝ 2 (fun z => toProjectiveState (F (z, τ z))) z₀ := by
    convert! hto.comp z₀ hcEnd using 1
  have hcOut : ContDiffAt ℝ 2 (fun z => coreSectionCoordinates (toProjectiveState (F (z, τ z)))) z₀ := by
    convert! (contDiff_coreSectionCoordinates 2).contDiffAt.comp z₀ hcProjective using 1
  have heq : P =ᶠ[𝓝 z₀] (fun z => coreSectionCoordinates (toProjectiveState (F (z, τ z)))) := by
    filter_upwards [hfirst] with z hz
    change P z = coreSectionCoordinates (toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (τ z)))
    rw [hz.2.2.2.2]
    ext i
    fin_cases i <;> rfl
  exact ⟨τ, P, hτ, hP, hτ2, hcOut.congr_of_eventuallyEq heq, hfirst, hdP⟩
