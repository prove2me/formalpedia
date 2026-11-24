-- Prove2me | solution 1 for FairSelling.PhaseTPS.plarge_pure_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:44:58.134144+00:00
-- url     : https://prove2.me/submissions/a9286fe7-5ba8-4bb2-97dc-d6b2f3dbf044

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPhaseStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPhaseImp
import Theorems.Thm_FairSelling_PhaseTPS_preq_nonneg
import Theorems.Thm_FairSelling_PhaseTPS_preq_eq_thr
import Theorems.Thm_FairSelling_PhaseTPS_pmoney_step
import Theorems.Thm_FairSelling_CfgTPS_Qc_empty_le
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_TPS_le_two_thr
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bank
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_bundle
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_cash
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_resv
import Theorems.Thm_FairSelling_PhaseTPS_PStage_toCStage_served
import Theorems.Thm_FairSelling_PhaseTPS_pureGood_of_TPS_le
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
    {s : PStage G n} (hs : s.Good v p eps) {k0 : Fin n} (hk0 : k0 ∉ s.served)
    {g : G} (hg : g ∈ s.pool)
    (hbig : ∀ j, j ∉ s.served → 2 * GeneralTPS.thr v p j < p g) :
    ∃ s' : PStage G n, s'.Good v p eps ∧
      (s.served.card < s'.served.card ∨
        (s.served.card = s'.served.card ∧ s.total v p + eps ≤ s'.total v p)) := by
  classical
  have hpure : PureGood v p s.served g :=
    pureGood_of_TPS_le (fun j hj => by
      have h1 := ChargeTPS.TPS_le_two_thr v p hn hp j
      have h2 := hbig j hj
      linarith)
  refine pmoney_step v p eps hcarrier hn hp heps hs k0 (Finset.singleton_subset_iff.mpr hg)
    (fun x hx => by rwa [Finset.mem_singleton.mp hx]) ?_
  -- the slice is smaller than the price of the good
  have hreq0 : ∀ m, 0 ≤ s.req v p eps m := preq_nonneg v p eps hn hp heps hs
  have h1 : CfgTPS.Qc v p (s.req v p eps) k0 (∅ : Finset G) ≤ s.req v p eps k0 :=
    CfgTPS.Qc_empty_le (w := v) (p := p) (k0 := k0) hreq0 k0
  rw [preq_eq_thr v p eps hk0] at h1
  have h2 := hbig k0 hk0
  have h3 := GeneralTPS.thr_nonneg v p hn hp k0
  have h4 := hs.bank_nonneg
  simp only [Finset.sum_singleton]
  linarith
end FairSelling.PhaseTPS
