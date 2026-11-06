-- Prove2me | solution 1 for BianchiIX.exists_referenceCore_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:53:21.824219+00:00
-- url     : https://prove2.me/submissions/76a9828c-db11-418a-86ae-5afc4e6ad1b0

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Theorems.Thm_BianchiIX_contDiff_projectiveField
import Theorems.Thm_BianchiIX_continuous_projectiveStateDenom
import Theorems.Thm_BianchiIX_eventually_referenceCore_above_section
import Theorems.Thm_BianchiIX_eventually_referenceCore_interval_regular
import Theorems.Thm_BianchiIX_exists_referenceCore_section_event
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv_field
import Theorems.Thm_BianchiIX_referenceCoreGap_pos
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_referencePulse_exit
import Theorems.Thm_BianchiIX_referencePulse_exit_field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
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

private theorem BianchiIX.referenceCoreInput_embedding {k : ℝ} (hk : 1 < k) :
    coreSectionEmbedding (referenceCoreInput k) = referencePulse k (-referenceHalfTime k) := by
  rw [referencePulse_entry hk]
  rfl

end
end

private theorem BianchiIX.eventually_referenceCore_chart_denom_pos {k : ℝ} (hk : 1 < k) :
    ∀ᶠ z in 𝓝 (referenceCoreInput k), 0 < projectiveStateDenom (coreSectionEmbedding z) := by
  have hc : Continuous (fun z => projectiveStateDenom (coreSectionEmbedding z)) :=
    continuous_projectiveStateDenom.comp (contDiff_coreSectionEmbedding 1).continuous
  apply hc.continuousAt.eventually (isOpen_Ioi.mem_nhds _)
  change 0 < projectiveStateDenom (coreSectionEmbedding (referenceCoreInput k))
  rw [referenceCoreInput_embedding hk]
  exact referencePulse_denom_pos k _

/-- Near each reference pulse, the differentiable exit map is the actual first positive return. -/
theorem solution {k : ℝ} (hk : 1 < k) :
    ∃ (tau : CoreCoordinates → ℝ) (P : CoreCoordinates → CoreCoordinates),
      tau (referenceCoreInput k) = referenceNormalizedTime k ∧
      P (referenceCoreInput k) = referenceCoreOutput k ∧
      ContDiffAt ℝ 1 tau (referenceCoreInput k) ∧ ContDiffAt ℝ 1 P (referenceCoreInput k) ∧
      (∀ᶠ z in 𝓝 (referenceCoreInput k),
        IsLeast {t : ℝ | 0 < t ∧ t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
          projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t) = 1} (tau z) ∧
        (∀ t ∈ Icc 0 (tau z), t ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
          0 < 1 + normalizedMaxCurve (coreSectionChart z) 0 t 0) ∧
        (∀ t ∈ Ioo 0 (tau z), 1 < projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t)) ∧
        normalizedEventRate projectiveActiveWall (coreSectionChart z) 0 (tau z) < 0 ∧
        toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (tau z)) = coreSectionEmbedding (P z)) ∧
      (∀ v : CoreCoordinates, fderiv ℝ P (referenceCoreInput k) v =
        ![-v 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * v 1,
          Real.exp (-k * Real.arcosh k) * v 1, Real.exp (-4 * Real.arcosh k / k) * v 2]) := by
  obtain ⟨tau, P, hτ, hP, hcτ, hcP, hhit, huniq, hdP⟩ := exists_referenceCore_section_event hk
  have habove := eventually_referenceCore_above_section hk hτ hcτ.continuousAt
    (huniq.mono fun _ h => h.2.mp)
  have hregular := eventually_referenceCore_interval_regular hk hτ hcτ.continuousAt
  have hdir : ∀ᶠ z in 𝓝 (referenceCoreInput k), projectiveField (coreSectionEmbedding (P z)) 2 < 0 := by
    have hemb : ContinuousAt (fun z => coreSectionEmbedding (P z)) (referenceCoreInput k) :=
      ContinuousAt.comp (f := P) (g := coreSectionEmbedding)
        (contDiff_coreSectionEmbedding 1).continuous.continuousAt hcP.continuousAt
    have hf : ContinuousAt (fun z => projectiveField (coreSectionEmbedding (P z))) (referenceCoreInput k) :=
      ContinuousAt.comp (f := fun z => coreSectionEmbedding (P z)) (g := projectiveField)
        (contDiff_projectiveField 1).continuous.continuousAt hemb
    apply (continuousAt_pi.mp hf 2).eventually (isOpen_Iio.mem_nhds _)
    change projectiveField (coreSectionEmbedding (P (referenceCoreInput k))) 2 < 0
    rw [hP]
    have heq : coreSectionEmbedding (referenceCoreOutput k) = referencePulse k (referenceHalfTime k) := by
      rw [referencePulse_exit hk]
      rfl
    rw [heq, referencePulse_exit_field hk]
    exact neg_neg_of_pos (referenceCoreGap_pos hk)
  refine ⟨tau, P, hτ, hP, hcτ, hcP, ?_, hdP⟩
  filter_upwards [hhit, habove, hregular, hdir, eventually_referenceCore_chart_denom_pos hk]
    with z hz hhigh hreg hdown hD
  refine ⟨⟨⟨hz.1, hz.2.1, ?_⟩, ?_⟩, hreg, hhigh, ?_, hz.2.2⟩
  · change toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (tau z)) 2 = 1
    rw [hz.2.2]
    rfl
  · intro t ht
    by_contra! hlt
    exact (ne_of_gt (hhigh t ⟨ht.1, hlt⟩)) ht.2.2
  · have hA := (hreg (tau z) ⟨hz.1.le, le_rfl⟩).2
    have hc : stateConstraint (normalizedMaxCurve (coreSectionChart z) 0 (tau z)) = 1 := by
      rw [normalizedMaxCurve_constraint hz.2.1]
      exact fromProjectiveState_constraint (ne_of_gt hD)
    rw [normalizedEventRate, projectiveActiveWall_fderiv_field (ne_of_gt hA) hc, hz.2.2]
    exact mul_neg_of_pos_of_neg hA hdown
