-- Prove2me | solution 1 for BianchiIX.eventually_referenceCore_entry_unique
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:48:41.34419+00:00
-- url     : https://prove2.me/submissions/f110a522-aef4-4fe8-8215-8ad906b42728

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_continuous_projectiveStateDenom
import Theorems.Thm_BianchiIX_exists_normalized_event
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv_field
import Theorems.Thm_BianchiIX_referenceCoreGap_pos
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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

private theorem BianchiIX.contDiffAt_referenceCoreChart {k : ℝ} (hk : 1 < k) (n : WithTop ℕ∞) :
    ContDiffAt ℝ n coreSectionChart (referenceCoreInput k) := by
  have hf := contDiffAt_fromProjectiveState n
    (ne_of_gt (referencePulse_denom_pos k (-referenceHalfTime k)))
  rw [← referenceCoreInput_embedding hk] at hf
  exact hf.comp _ (contDiff_coreSectionEmbedding n).contDiffAt

private theorem BianchiIX.eventually_referenceCore_chart_denom_pos {k : ℝ} (hk : 1 < k) :
    ∀ᶠ z in 𝓝 (referenceCoreInput k), 0 < projectiveStateDenom (coreSectionEmbedding z) := by
  have hc : Continuous (fun z => projectiveStateDenom (coreSectionEmbedding z)) :=
    continuous_projectiveStateDenom.comp (contDiff_coreSectionEmbedding 1).continuous
  apply hc.continuousAt.eventually (isOpen_Ioi.mem_nhds _)
  change 0 < projectiveStateDenom (coreSectionEmbedding (referenceCoreInput k))
  rw [referenceCoreInput_embedding hk]
  exact referencePulse_denom_pos k _

private theorem BianchiIX.continuousAt_coreSection_pair {z : CoreCoordinates} {t : ℝ}
    (hc : ContinuousAt coreSectionChart z) :
    ContinuousAt (fun q : CoreCoordinates × ℝ => (coreSectionChart q.1, q.2)) (z, t) := by
  have hfst : ContinuousAt (fun q : CoreCoordinates × ℝ => coreSectionChart q.1) (z, t) := by
    have hf : ContinuousAt (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates) (z, t) := continuousAt_fst
    exact ContinuousAt.comp (f := (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates))
      (g := coreSectionChart) hc hf
  exact hfst.prodMk continuousAt_snd

private theorem BianchiIX.referenceEntryState_rate_pos {k : ℝ} (hk : 1 < k) :
    fderiv ℝ projectiveActiveWall (referenceEntryState k) (normalizedField (referenceEntryState k)) > 0 := by
  have hA : 0 < 1 + referenceEntryState k 0 :=
    fromProjectiveState_clock_pos (referencePulse_denom_pos k _)
  have hc : stateConstraint (referenceEntryState k) = 1 :=
    fromProjectiveState_constraint (ne_of_gt (referencePulse_denom_pos k _))
  rw [projectiveActiveWall_fderiv_field (ne_of_gt hA) hc]
  have hproj : toProjectiveState (referenceEntryState k) = referencePulse k (-referenceHalfTime k) :=
    toProjectiveState_fromProjectiveState (ne_of_gt (referencePulse_denom_pos k _))
  rw [hproj, referencePulse_entry hk]
  simpa [projectiveField, activeVelocity, coupling] using mul_pos hA (referenceCoreGap_pos hk)

/-- The section itself fixes the locally unique entry event at time zero. -/
theorem solution {k : ℝ} (hk : 1 < k) :
    ∀ᶠ q : CoreCoordinates × ℝ in 𝓝 (referenceCoreInput k, 0),
      projectiveActiveWall (normalizedMaxCurve (coreSectionChart q.1) 0 q.2) = 1 → q.2 = 0 := by
  let z₀ := referenceCoreInput k
  have hbase := referenceCoreInput_chart hk
  have hchart := (contDiffAt_referenceCoreChart hk 1).continuousAt
  have hA : 0 < 1 + referenceEntryState k 0 :=
    fromProjectiveState_clock_pos (referencePulse_denom_pos k _)
  have hg : ContDiffAt ℝ 1 projectiveActiveWall (normalizedMaxCurve (referenceEntryState k) 0 0) := by
    rw [normalizedMaxCurve_initial]
    exact contDiffAt_projectiveActiveWall 1 (ne_of_gt hA)
  have hr : normalizedEventRate projectiveActiveWall (referenceEntryState k) 0 0 ≠ 0 := by
    simpa only [normalizedEventRate, normalizedMaxCurve_initial] using
      ne_of_gt (referenceEntryState_rate_pos hk)
  have hv : projectiveActiveWall (normalizedMaxCurve (referenceEntryState k) 0 0) = 1 := by
    rw [normalizedMaxCurve_initial]
    unfold projectiveActiveWall referenceEntryState
    rw [toProjectiveState_fromProjectiveState (ne_of_gt (referencePulse_denom_pos k _)),
      referencePulse_entry hk]
    rfl
  obtain ⟨T, _, _, _, _, huniq, _, _⟩ :=
    exists_normalized_event (initial_mem_normalizedMaxDomain (referenceEntryState k) 0) hg hr
  have hmap : ContinuousAt (fun q : CoreCoordinates × ℝ => (coreSectionChart q.1, q.2)) (z₀, 0) :=
    continuousAt_coreSection_pair hchart
  have hlocal : ∀ᶠ q : CoreCoordinates × ℝ in 𝓝 (z₀, 0),
      projectiveActiveWall (normalizedMaxCurve (coreSectionChart q.1) 0 q.2) = 1 ↔
        T (coreSectionChart q.1) = q.2 := by
    have H := hmap.eventually (hbase.symm ▸ huniq)
    filter_upwards [H] with q hq
    simpa only [hbase, hv] using hq.2
  have hzero : ∀ᶠ z in 𝓝 z₀, T (coreSectionChart z) = 0 := by
    have hzmap : ContinuousAt (fun z : CoreCoordinates => (z, (0 : ℝ))) z₀ :=
      continuousAt_id.prodMk continuousAt_const
    filter_upwards [hzmap.eventually hlocal, eventually_referenceCore_chart_denom_pos hk] with z hz hdz
    apply hz.mp
    rw [normalizedMaxCurve_initial]
    unfold projectiveActiveWall coreSectionChart
    rw [toProjectiveState_fromProjectiveState (ne_of_gt hdz)]
    rfl
  have hzprod : ∀ᶠ q : CoreCoordinates × ℝ in 𝓝 (z₀, 0), T (coreSectionChart q.1) = 0 := by
    have hf : ContinuousAt (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates) (z₀, 0) := continuousAt_fst
    exact hf.eventually hzero
  filter_upwards [hlocal, hzprod] with q hq hz
  intro heq
  exact (hq.mp heq).symm.trans hz
