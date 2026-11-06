-- Prove2me | solution 1 for BianchiIX.referencePulse_normalized_crossing
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:04:40.034145+00:00
-- url     : https://prove2.me/submissions/da37d199-476f-4644-a7f4-1c749ff612d9

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Theorems.Thm_BianchiIX_exists_projective_normalized_reparametrization
import Theorems.Thm_BianchiIX_hasDerivAt_referencePulse
import Theorems.Thm_BianchiIX_integralClock_initial
import Theorems.Thm_BianchiIX_referencePulse_above_section
import Theorems.Thm_BianchiIX_referencePulse_crossing_time
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
import Theorems.Thm_BianchiIX_referencePulse_entry
import Theorems.Thm_BianchiIX_referencePulse_exit
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

noncomputable section
open BianchiIX
open Set MeasureTheory


/-- The entire first crossing is realized by the original maximal flow. -/
theorem solution {k : ℝ} (hk : 1 < k) :
    Icc 0 (referenceNormalizedTime k) ⊆ normalizedMaxDomain
      (fromProjectiveState ![1 + Real.sqrt (k ^ 2 - 1), 0, 1, 0]) 0 ∧
    normalizedMaxCurve (fromProjectiveState ![1 + Real.sqrt (k ^ 2 - 1), 0, 1, 0]) 0
      (referenceNormalizedTime k) =
      fromProjectiveState ![1 - Real.sqrt (k ^ 2 - 1), 0, 1, 0] ∧
    ∀ t ∈ Ioo 0 (referenceNormalizedTime k),
      1 < toProjectiveState (normalizedMaxCurve
        (fromProjectiveState ![1 + Real.sqrt (k ^ 2 - 1), 0, 1, 0]) 0 t) 2 := by
  obtain ⟨e, hsrc, he, _, hconv, hzero, _, hmono, hdom, hflow⟩ :=
    exists_projective_normalized_reparametrization (β := referencePulse k)
      (s := -referenceHalfTime k) convex_univ isOpen_univ (mem_univ _)
      (fun t _ => hasDerivAt_referencePulse k t) (fun t _ => referencePulse_denom_pos k t)
  have hmem : referenceHalfTime k ∈ e.source := by rw [hsrc]; trivial
  have ht : e (referenceHalfTime k) = referenceNormalizedTime k := by
    rw [he, referencePulse_crossing_time k]
  have htarget : referenceNormalizedTime k ∈ e.target := ht ▸ e.map_source hmem
  have hinter : Icc 0 (referenceNormalizedTime k) ⊆ e.target :=
    (Icc_subset_uIcc ..).trans (hconv.ordConnected.uIcc_subset hzero htarget)
  have hbase : e (-referenceHalfTime k) = 0 := by
    rw [he]
    exact integralClock_initial _ _
  have hinv : e.symm (referenceNormalizedTime k) = referenceHalfTime k := by
    rw [← ht, e.left_inv hmem]
  have h := (hflow _ htarget).1
  rw [hinv, referencePulse_entry hk, referencePulse_exit hk] at h
  refine ⟨by simpa only [referencePulse_entry hk] using hinter.trans hdom, h.symm, ?_⟩
  intro t htt
  have htg : t ∈ e.target := hinter ⟨htt.1.le, htt.2.le⟩
  have hleft : -referenceHalfTime k < e.symm t := by
    by_contra! hn
    have H := hmono.monotoneOn (mem_univ (e.symm t)) (mem_univ (-referenceHalfTime k)) hn
    rw [e.right_inv htg, hbase] at H
    exact (not_le_of_gt htt.1) H
  have hright : e.symm t < referenceHalfTime k := by
    by_contra! hn
    have H := hmono.monotoneOn (mem_univ (referenceHalfTime k)) (mem_univ (e.symm t)) hn
    rw [e.right_inv htg, ht] at H
    exact (not_le_of_gt htt.2) H
  have H := (hflow t htg).2
  rw [referencePulse_entry hk] at H
  rw [H]
  exact referencePulse_above_section hk ⟨hleft, hright⟩
