-- Prove2me | solution 1 for FairSelling.PhaseTPS.pmoney_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:52:02.340112+00:00
-- url     : https://prove2.me/submissions/e4e76e7d-dadc-4525-8cf7-d933afde81bf

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Theorems.Thm_FairSelling_PhaseTPS_preq_nonneg
import Theorems.Thm_FairSelling_PhaseTPS_preq_eq_thr
import Theorems.Thm_FairSelling_CfgTPS_Qc_claimed
import Theorems.Thm_FairSelling_CfgTPS_Qc_empty_le
import Theorems.Thm_FairSelling_CfgTPS_Qc_nonneg
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_PhaseTPS_PureGood_mono
import Theorems.Thm_FairSelling_PhaseTPS_pstep_assign_any
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_bank
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_bundle
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_cash
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_resv
attribute [local simp] FairSelling.PhaseTPS.PStage.toCStage_served
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PhaseTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PhaseTPS
theorem _root_.solution (hcarrier : PCarrierReassign v p eps)
    (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : PStage G n} (hs : s.Good v p eps) (k0 : Fin n)
    {F : Finset G} (hFpool : F ⊆ s.pool)
    (hFpure : ∀ g ∈ F, PureGood v p s.served g)
    (hafford : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.bank + ∑ g ∈ F, p g) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  set q := CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) with hq
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 (∅ : Finset G)
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := preq_nonneg v p eps hn hp heps hs
  have hqreq : ∀ m, q ≤ s.req v p eps m := fun m =>
    CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 m
  have hq0 : 0 ≤ q := CfgTPS.Qc_nonneg v p (s.req v p eps) k0 _
  have hthr0 : ∀ j, 0 ≤ GeneralTPS.thr v p j := GeneralTPS.thr_nonneg v p hn hp
  have hE : 0 ≤ s.cash k + s.resv k - ∑ x ∈ s.own k, p x := by
    have := hs.self_fin k; linarith
  have hpure' : ∀ x ∈ F, PureGood v p (insert k s.served) x :=
    fun x hx => PureGood.mono (Finset.subset_insert k s.served) (hFpure x hx)
  have hclaim' : s.req v p eps k ≤ vbarSum (v k) p ∅ + q := by simpa [vbarSum] using hclaim
  refine pstep_assign_any v p eps hcarrier hn hp heps hs (S := ∅) (S₀own := ∅) (S₀ext := F)
    (by simp) (by simp) hFpool
    (by simp) (by simp) (by simp) (q := q) (r := 0) hq0 le_rfl ?_ (by simpa using hq0)
    (Or.inl hpure') hclaim' (by simp) ?_ ?_
  · -- the slice is affordable
    simp only [Finset.sum_empty, add_zero]
    linarith
  · -- the slice is safe for everybody
    intro j _
    left
    simpa [vbarSum] using hqreq j
  · -- the slice costs every unserved agent at most its threshold
    intro j hj
    have hj' : j ∉ s.served := fun h => hj (Finset.mem_insert_of_mem h)
    have h1 : q ≤ s.req v p eps j := hqreq j
    rw [preq_eq_thr v p eps hj'] at h1
    have := hthr0 j
    simp only [truncBundle, Finset.sum_empty, zero_add, add_zero]
    linarith
end FairSelling.PhaseTPS
