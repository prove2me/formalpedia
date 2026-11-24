-- Prove2me | solution 1 for FairSelling.PotTPS.qfeas_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:54:38.181511+00:00
-- url     : https://prove2.me/submissions/01f83b53-8351-4ad9-900d-714d93ba6546

import Mathlib
import Definitions.Def_RequestProject_TPSSefxPotStep
import Definitions.Def_RequestProject_TPSSefxStep
import Definitions.Def_RequestProject_TPSSefxPotImp
import Theorems.Thm_FairSelling_CfgTPS_Qc_le_of_gap
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_req_eq_thr
import Theorems.Thm_FairSelling_GeneralTPS_thr_nonneg
import Theorems.Thm_FairSelling_PotTPS_QStage_freeBank_nonneg_of
import Theorems.Thm_FairSelling_PotTPS_QStage_qcounting
import Theorems.Thm_FairSelling_PotTPS_QStage_req_eq_thr
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_bundle
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_cash
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_served
import Theorems.Thm_FairSelling_PotTPS_QStage_toStage_soldSet
import Theorems.Thm_FairSelling_restrictVal_mem
import Theorems.Thm_FairSelling_truncBundle_le_vbarSum
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
theorem _root_.solution (hn : 0 < n) (hp : ∀ g, 0 ≤ p g) {s : QStage G n} (hs : s.Good v p eps)
    {k0 : Fin n} (hk0 : k0 ∉ s.served)
    (hsmall : ∀ g ∈ s.cutSet, s.pot p g ≤ GeneralTPS.thr v p k0) :
    CfgTPS.Feas v p (s.req v p eps) k0 (s.freeBank p) s.pool ∅ := by
  classical
  have hcount := QStage.qcounting hn hp hs k0 hk0
  have hthr : 0 ≤ GeneralTPS.thr v p k0 := GeneralTPS.thr_nonneg v p hn hp k0
  have hmin : ∑ g ∈ s.cutSet, min (s.pot p g) (GeneralTPS.thr v p k0)
      = ∑ g ∈ s.cutSet, s.pot p g :=
    Finset.sum_congr rfl (fun g hg => min_eq_left (hsmall g hg))
  have hcard : (s.served.card : ℝ) ≤ (n : ℝ) - 1 := by
    have h1 : s.served.card < n := by
      have h2 : s.served ⊂ Finset.univ :=
        ⟨Finset.subset_univ _, fun h => hk0 (h (Finset.mem_univ k0))⟩
      simpa using Finset.card_lt_card h2
    have : (s.served.card : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast h1
    linarith
  have hmul : GeneralTPS.thr v p k0
      ≤ (2 * ((n : ℝ) - s.served.card) - 1) * GeneralTPS.thr v p k0 := by nlinarith
  have hle : truncBundle (v k0) p (TPS n (v k0) p) s.pool ≤ vbarSum (v k0) p s.pool :=
    truncBundle_le_vbarSum _ _ _ _
  have hreq : s.req v p eps k0 = GeneralTPS.thr v p k0 := QStage.req_eq_thr hk0
  have hfreeeq : s.freeBank p = s.bank - ∑ g ∈ s.cutSet, s.pot p g := rfl
  unfold CfgTPS.Feas
  simp only [Finset.sum_empty, add_zero]
  refine CfgTPS.Qc_le_of_gap v p (s.req v p eps) k0 (QStage.freeBank_nonneg_of hs) k0 ?_
  rw [hreq, hfreeeq]
  rw [hmin] at hcount
  linarith
end FairSelling.PotTPS
