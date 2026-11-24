-- Prove2me | solution 1 for FairSelling.PotTPS.qcut_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:59:20.437919+00:00
-- url     : https://prove2.me/submissions/3b0dcfc1-88db-441b-9109-06734e4230a4

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPotStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPotImp
import Theorems.Thm_FairSelling_CfgTPS_Qc_claimed
import Theorems.Thm_FairSelling_CfgTPS_Qc_empty_le
import Theorems.Thm_FairSelling_CfgTPS_Qc_nonneg
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_req_eq_thr
import Theorems.Thm_FairSelling_ChargeTPS_req_nonneg
import Theorems.Thm_FairSelling_PotTPS_QStage_req_eq_thr
import Theorems.Thm_FairSelling_PotTPS_QStage_req_nonneg
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_bundle
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_cash
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_soldSet
import Theorems.Thm_FairSelling_PotTPS_qstep_assign
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.PotTPS.QStage.toStage_bundle
attribute [local simp] FairSelling.PotTPS.QStage.toStage_cash
attribute [local simp] FairSelling.PotTPS.QStage.toStage_served
attribute [local simp] FairSelling.PotTPS.QStage.toStage_soldSet
attribute [local simp] FairSelling.restrictVal_mem



set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.PotTPS
open ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
variable (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ)
namespace FairSelling.PotTPS
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) (heps : 0 ≤ eps)
    {s : QStage G n} (hs : s.Good v p eps) (k0 : Fin n) {g0 : G} (hg0 : g0 ∈ s.cutSet)
    (hqle : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.pot p g0) :
    ∃ s' : QStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  set q := CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) with hqdef
  obtain ⟨k, hclaim⟩ := CfgTPS.Qc_claimed v p (s.req v p eps) k0 (∅ : Finset G)
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := fun m => QStage.req_nonneg hn hp heps hs m
  have hqreq : ∀ m, q ≤ s.req v p eps m := fun m =>
    CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 m
  have hq0 : 0 ≤ q := CfgTPS.Qc_nonneg v p (s.req v p eps) k0 _
  have hclaim' : s.req v p eps k ≤ vbarSum (v k) p ∅ + q := by simpa [vbarSum] using hclaim
  refine qstep_assign v p eps hn hp heps hs (S := ∅) (S₀ := ∅) (Src := {g0}) (Snew := ∅)
    (by simp) (by simp) (by simp) hq0 le_rfl (by simp) (fun _ => ⟨rfl, rfl, rfl⟩)
    (Or.inl rfl) (fun _ => Finset.singleton_subset_iff.mpr hg0) ?_ ?_ (by simp) (by simpa using hq0)
    hclaim' (by simp) ?_ (by simp)
  · intro g hg
    rw [Finset.mem_singleton.mp hg]
    exact hqle
  · intro _ j hj
    have h1 := hqreq j
    rwa [QStage.req_eq_thr hj] at h1
  · intro j _
    left
    simpa [vbarSum] using hqreq j
end FairSelling.PotTPS
