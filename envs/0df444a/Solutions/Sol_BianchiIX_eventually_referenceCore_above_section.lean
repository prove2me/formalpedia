-- Prove2me | solution 1 for BianchiIX.eventually_referenceCore_above_section
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:51:49.567863+00:00
-- url     : https://prove2.me/submissions/c67b7d1c-b2cd-4474-a5e9-eb7010214d74

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ReferenceActualVariation
import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_projectiveActiveWall
import Theorems.Thm_BianchiIX_eventually_referenceCore_interval_regular
import Theorems.Thm_BianchiIX_eventually_referenceCore_no_intermediate_return
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_hasDerivAt_referenceClockPrimitive
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_referenceClock_normalized_orbit
import Theorems.Thm_BianchiIX_referenceHalfTime_pos
import Theorems.Thm_BianchiIX_referenceNormalizedTime_pos
import Theorems.Thm_BianchiIX_referencePulse_clock_integral
import Theorems.Thm_BianchiIX_referencePulse_crossing_time
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_referencePulse_normalized_crossing
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
variable {X : Type*} [TopologicalSpace X]

private theorem BianchiIX.strict_above_of_no_return {a b c m : ℝ} {f : ℝ → ℝ}
    (hc : ContinuousOn f (Ioo a b)) (hm : m ∈ Ioo a b) (hmid : c < f m)
    (hne : ∀ t ∈ Ioo a b, f t ≠ c) : ∀ t ∈ Ioo a b, c < f t := by
  intro t ht
  by_contra! hle
  obtain ⟨s, hs, heq⟩ := isPreconnected_Ioo.intermediate_value ht hm hc ⟨hle, hmid.le⟩
  exact hne s hs heq

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_referenceClock (k t : ℝ) :
    HasDerivAt (referenceClock k) (projectiveStateDenom (referencePulse k t) / 6) t :=
  (hasDerivAt_referenceClockPrimitive k t).sub_const _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceClock_entry (k : ℝ) : referenceClock k (-referenceHalfTime k) = 0 := sub_self _

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceClock_exit (k : ℝ) :
    referenceClock k (referenceHalfTime k) = referenceNormalizedTime k := by
  rw [referenceClock, ← referencePulse_clock_integral, referencePulse_crossing_time]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.referenceClock_chart_pos (k t : ℝ) :
    0 < 1 + normalizedMaxCurve (referenceEntryState k) 0 (referenceClock k t) 0 := by
  rw [(referenceClock_normalized_orbit k t).2]
  exact fromProjectiveState_clock_pos (referencePulse_denom_pos k t)

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

private theorem BianchiIX.referenceCore_interval_regular {k t : ℝ} (hk : 1 < k)
    (ht : t ∈ Icc 0 (referenceNormalizedTime k)) :
    t ∈ normalizedMaxDomain (coreSectionChart (referenceCoreInput k)) 0 ∧
      0 < 1 + normalizedMaxCurve (coreSectionChart (referenceCoreInput k)) 0 t 0 := by
  have hc : Continuous (referenceClock k) :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_referenceClock k s).continuousAt
  have hends : -referenceHalfTime k ≤ referenceHalfTime k := by
    linarith [referenceHalfTime_pos hk]
  have hm : t ∈ Icc (referenceClock k (-referenceHalfTime k))
      (referenceClock k (referenceHalfTime k)) := by
    simpa only [referenceClock_entry, referenceClock_exit] using ht
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc hends hc.continuousOn hm
  rw [referenceCoreInput_chart hk, ← hs]
  exact ⟨(referenceClock_normalized_orbit k s).1, referenceClock_chart_pos k s⟩

private theorem BianchiIX.continuousAt_coreSection_pair {z : CoreCoordinates} {t : ℝ}
    (hc : ContinuousAt coreSectionChart z) :
    ContinuousAt (fun q : CoreCoordinates × ℝ => (coreSectionChart q.1, q.2)) (z, t) := by
  have hfst : ContinuousAt (fun q : CoreCoordinates × ℝ => coreSectionChart q.1) (z, t) := by
    have hf : ContinuousAt (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates) (z, t) := continuousAt_fst
    exact ContinuousAt.comp (f := (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates))
      (g := coreSectionChart) hc hf
  exact hfst.prodMk continuousAt_snd

private theorem BianchiIX.continuousAt_coreFlow {z : CoreCoordinates} {t : ℝ}
    (hc : ContinuousAt coreSectionChart z)
    (ht : t ∈ normalizedMaxDomain (coreSectionChart z) 0) :
    ContinuousAt (fun q : CoreCoordinates × ℝ =>
      normalizedMaxCurve (coreSectionChart q.1) 0 q.2) (z, t) := by
  exact ContinuousAt.comp (g := fun q : NormalizedState × ℝ => normalizedMaxCurve q.1 0 q.2)
    (f := fun q : CoreCoordinates × ℝ => (coreSectionChart q.1, q.2))
    (normalizedMaxCurve_regular ht).2.continuousAt (continuousAt_coreSection_pair hc)

theorem solution {k : ℝ} (hk : 1 < k)
    {tau : CoreCoordinates → ℝ}
    (hτ : tau (referenceCoreInput k) = referenceNormalizedTime k)
    (hcτ : ContinuousAt tau (referenceCoreInput k))
    (huniq : ∀ᶠ q : CoreCoordinates × ℝ in 𝓝 (referenceCoreInput k, referenceNormalizedTime k),
      projectiveActiveWall (normalizedMaxCurve (coreSectionChart q.1) 0 q.2) = 1 → tau q.1 = q.2) :
    ∀ᶠ z in 𝓝 (referenceCoreInput k), ∀ t ∈ Ioo 0 (tau z),
      1 < projectiveActiveWall (normalizedMaxCurve (coreSectionChart z) 0 t) := by
  have hmid : referenceNormalizedTime k / 2 ∈ Ioo 0 (referenceNormalizedTime k) := by
    constructor <;> linarith [referenceNormalizedTime_pos hk]
  obtain ⟨hdom, hpos⟩ := referenceCore_interval_regular hk ⟨hmid.1.le, hmid.2.le⟩
  have hflow := continuousAt_coreFlow (contDiffAt_referenceCoreChart hk 1).continuousAt hdom
  have hobs : ContinuousAt (fun q : CoreCoordinates × ℝ =>
      projectiveActiveWall (normalizedMaxCurve (coreSectionChart q.1) 0 q.2))
      (referenceCoreInput k, referenceNormalizedTime k / 2) :=
    ContinuousAt.comp (f := fun q : CoreCoordinates × ℝ => normalizedMaxCurve (coreSectionChart q.1) 0 q.2)
      (g := projectiveActiveWall) (contDiffAt_projectiveActiveWall 1 (ne_of_gt hpos)).continuousAt hflow
  have hv : 1 < projectiveActiveWall
      (normalizedMaxCurve (coreSectionChart (referenceCoreInput k)) 0 (referenceNormalizedTime k / 2)) := by
    simpa only [projectiveActiveWall, referenceCoreInput_chart hk, referenceEntryState,
      referencePulse_entry hk] using (referencePulse_normalized_crossing hk).2.2 _ hmid
  have hgraph : Tendsto (fun z : CoreCoordinates => (z, tau z / 2))
      (𝓝 (referenceCoreInput k)) (𝓝 (referenceCoreInput k, referenceNormalizedTime k / 2)) := by
    have H : ContinuousAt (fun z : CoreCoordinates => (z, tau z / 2)) (referenceCoreInput k) :=
      continuousAt_id.prodMk (hcτ.div_const 2)
    simpa only [hτ] using H.tendsto
  have hmiddle := hgraph.eventually (hobs.eventually (isOpen_Ioi.mem_nhds hv))
  have hpositive : ∀ᶠ z in 𝓝 (referenceCoreInput k), 0 < tau z :=
    hcτ.eventually (isOpen_Ioi.mem_nhds (by rw [hτ]; exact referenceNormalizedTime_pos hk))
  filter_upwards [hmiddle, hpositive, eventually_referenceCore_interval_regular hk hτ hcτ,
    eventually_referenceCore_no_intermediate_return hk hτ hcτ huniq] with z hm hp hreg hno
  apply strict_above_of_no_return (m := tau z / 2) ?_ (by constructor <;> linarith) hm hno
  intro t ht
  obtain ⟨hd, hA⟩ := hreg t ⟨ht.1.le, ht.2.le⟩
  exact (ContinuousAt.comp (f := normalizedMaxCurve (coreSectionChart z) 0) (g := projectiveActiveWall)
    (contDiffAt_projectiveActiveWall 1 (ne_of_gt hA)).continuousAt
    (hasDerivAt_normalizedMaxCurve hd).continuousAt).continuousWithinAt
