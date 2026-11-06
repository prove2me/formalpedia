-- Prove2me | solution 1 for BianchiIX.exists_referenceCore_section_event
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:50:51.706982+00:00
-- url     : https://prove2.me/submissions/cee7c21b-1837-4cdb-919c-3ae1e0c544a2

import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ReferenceEvents
import Definitions.Def_BianchiIX_Dynamics_ReferenceSectionMap
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_coreSectionCoordinates_fderiv
import Theorems.Thm_BianchiIX_coreSectionEmbedding_fderiv
import Theorems.Thm_BianchiIX_exists_referenceCore_event
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_referenceCore_actual_derivative
import Theorems.Thm_BianchiIX_referenceNormalizedTime_pos
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_referencePulse_exit
import Theorems.Thm_BianchiIX_referencePulse_normalized_crossing
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
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

private theorem BianchiIX.referenceExitState_clock_pos (k : ℝ) : 0 < 1 + referenceExitState k 0 :=
  fromProjectiveState_clock_pos (referencePulse_denom_pos k _)

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

private theorem BianchiIX.contDiff_coreSectionEmbedding (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionEmbedding := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionEmbedding] <;> fun_prop

private theorem BianchiIX.contDiff_coreSectionCoordinates (n : WithTop ℕ∞) : ContDiff ℝ n coreSectionCoordinates := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreSectionCoordinates] <;> fun_prop

private theorem BianchiIX.referenceCoreInput_embedding {k : ℝ} (hk : 1 < k) :
    coreSectionEmbedding (referenceCoreInput k) = referencePulse k (-referenceHalfTime k) := by
  rw [referencePulse_entry hk]
  rfl

private theorem BianchiIX.referenceCoreInput_chart {k : ℝ} (hk : 1 < k) :
    coreSectionChart (referenceCoreInput k) = referenceEntryState k := by
  rw [coreSectionChart, referenceCoreInput_embedding hk]
  rfl

/-- A local three-coordinate exit map with the fully evaluated derivative of (A.4). -/
theorem solution {k : ℝ} (hk : 1 < k) :
    ∃ (tau : CoreCoordinates → ℝ) (P : CoreCoordinates → CoreCoordinates),
      tau (referenceCoreInput k) = referenceNormalizedTime k ∧
      P (referenceCoreInput k) = referenceCoreOutput k ∧
      ContDiffAt ℝ 1 tau (referenceCoreInput k) ∧ ContDiffAt ℝ 1 P (referenceCoreInput k) ∧
      (∀ᶠ z in 𝓝 (referenceCoreInput k), 0 < tau z ∧
        tau z ∈ normalizedMaxDomain (coreSectionChart z) 0 ∧
        toProjectiveState (normalizedMaxCurve (coreSectionChart z) 0 (tau z)) = coreSectionEmbedding (P z)) ∧
      (∀ᶠ z : CoreCoordinates × ℝ in 𝓝 (referenceCoreInput k, referenceNormalizedTime k),
        z.2 ∈ normalizedMaxDomain (coreSectionChart z.1) 0 ∧
        (projectiveActiveWall (normalizedMaxCurve (coreSectionChart z.1) 0 z.2) = 1 ↔ tau z.1 = z.2)) ∧
      (∀ v : CoreCoordinates, fderiv ℝ P (referenceCoreInput k) v =
        ![-v 0 + (2 / Real.sqrt (k ^ 2 - 1)) * (1 - Real.exp (-k * Real.arcosh k)) * v 1,
          Real.exp (-k * Real.arcosh k) * v 1, Real.exp (-4 * Real.arcosh k / k) * v 2]) := by
  let z₀ := referenceCoreInput k
  have hemb := referenceCoreInput_embedding hk
  have hbase := referenceCoreInput_chart hk
  have hcC : ContDiffAt ℝ 1 coreSectionChart z₀ := by
    have hf := contDiffAt_fromProjectiveState 1 (ne_of_gt (referencePulse_denom_pos k (-referenceHalfTime k)))
    rw [← hemb] at hf
    exact hf.comp z₀ (contDiff_coreSectionEmbedding 1).contDiffAt
  obtain ⟨T, hT, hcT, _, hhit, huniq, hcE, hdE⟩ := exists_referenceCore_event hk
  let E : NormalizedState → NormalizedState := fun y => normalizedMaxCurve y 0 (T y)
  let tau : CoreCoordinates → ℝ := fun z => T (coreSectionChart z)
  let P : CoreCoordinates → CoreCoordinates := fun z =>
    coreSectionCoordinates (toProjectiveState (E (coreSectionChart z)))
  have hE : E (coreSectionChart z₀) = referenceExitState k := by
    dsimp [E, z₀]
    rw [hbase, hT, (referenceEntryState_crossing hk).2]
  have hτ : tau z₀ = referenceNormalizedTime k := by dsimp [tau, z₀]; rw [hbase, hT]
  have hcτ : ContDiffAt ℝ 1 tau z₀ := (hbase.symm ▸ hcT).comp z₀ hcC
  have hto := contDiffAt_toProjectiveState 1 (ne_of_gt (referenceExitState_clock_pos k))
  have hcEC : ContDiffAt ℝ 1 (fun z => E (coreSectionChart z)) z₀ := by
    convert! (hbase.symm ▸ hcE).comp z₀ hcC using 1
  have hto' : ContDiffAt ℝ 1 toProjectiveState (E (coreSectionChart z₀)) := by rw [hE]; exact hto
  have hcP : ContDiffAt ℝ 1 P z₀ := by
    convert! (contDiff_coreSectionCoordinates 1).contDiffAt.comp z₀ (hto'.comp z₀ hcEC) using 1
  refine ⟨tau, P, hτ, ?_, hcτ, hcP, ?_, ?_, ?_⟩
  · dsimp [P]
    rw [hE, referenceExitState_projective, referencePulse_exit hk]
    rfl
  · have hpos : ∀ᶠ z in 𝓝 z₀, 0 < tau z :=
      (isOpen_Ioi.mem_nhds (show tau z₀ ∈ Ioi 0 by rw [hτ]; exact referenceNormalizedTime_pos hk))
        |> hcτ.continuousAt.eventually
    have hlocal := hcC.continuousAt.eventually (hbase.symm ▸ hhit)
    filter_upwards [hpos, hlocal] with z hz hloc
    refine ⟨hz, hloc.1, ?_⟩
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact hloc.2
    · rfl
  · have hmap : ContinuousAt (fun z : CoreCoordinates × ℝ => (coreSectionChart z.1, z.2))
        (z₀, referenceNormalizedTime k) := by
      have hfst : ContinuousAt (fun z : CoreCoordinates × ℝ => coreSectionChart z.1)
          (z₀, referenceNormalizedTime k) := by
        have hf : ContinuousAt (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates)
            (z₀, referenceNormalizedTime k) := continuousAt_fst
        exact ContinuousAt.comp (f := (Prod.fst : CoreCoordinates × ℝ → CoreCoordinates))
          (g := coreSectionChart) hcC.continuousAt hf
      exact hfst.prodMk continuousAt_snd
    have H := hmap.eventually (hbase.symm ▸ huniq)
    exact H
  · intro v
    have hdfrom := ((contDiffAt_fromProjectiveState 1
      (ne_of_gt (referencePulse_denom_pos k (-referenceHalfTime k)))).differentiableAt (by norm_num)).hasFDerivAt
    have hdemb := ((contDiff_coreSectionEmbedding 1).differentiable (by norm_num) z₀).hasFDerivAt
    have hdC' := (hemb.symm ▸ hdfrom).comp z₀ hdemb
    have hdE' := (hbase.symm ▸ hdE).comp z₀ hdC'
    have hdto := ((hE.symm ▸ hto).differentiableAt (by norm_num)).hasFDerivAt.comp z₀ hdE'
    have hdP := ((contDiff_coreSectionCoordinates 1).differentiable (by norm_num)
      (toProjectiveState (E (coreSectionChart z₀)))).hasFDerivAt.comp z₀ hdto
    rw [show fderiv ℝ P z₀ = _ from hdP.fderiv]
    simp only [ContinuousLinearMap.comp_apply, coreSectionCoordinates_fderiv,
      coreSectionEmbedding_fderiv, hE, hemb, hbase]
    rw [referenceCore_actual_derivative hk (w := ![v 0, v 1, 0, v 2]) rfl]
    rfl
