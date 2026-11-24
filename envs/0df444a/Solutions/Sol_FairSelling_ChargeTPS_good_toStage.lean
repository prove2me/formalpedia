-- Prove2me | solution 1 for FairSelling.ChargeTPS.good_toStage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:52.993136+00:00
-- url     : https://prove2.me/submissions/93288fa6-dfb7-42b8-a7dd-bd7dfd63b1d7

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_TPSSefxGeneral
import Definitions.Def_RequestProject_TPSSefxCharge
import Theorems.Thm_FairSelling_ChargeTPS_counting_of_cost
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_served
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_bundle
import Theorems.Thm_FairSelling_ChargeTPS_CStage_toStage_cash
import Theorems.Thm_FairSelling_restrictVal_mem
attribute [local simp] FairSelling.restrictVal_mem


attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_served
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_bundle
attribute [local simp] FairSelling.ChargeTPS.CStage.toStage_cash

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.ChargeTPS
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
open CStage
namespace FairSelling.ChargeTPS
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (eps : ℝ) (hn : 0 < n)
    (heps : 0 ≤ eps) (hp : ∀ g, 0 ≤ p g) {s : CStage G n} (hs : s.Good v p eps) :
    (s.toStage).Good v p eps := by
  classical
  obtain ⟨hempty, hbdisj, hcdisj, hcb, hcash0, hresv0, hbank0, hmoney, hshare, hsafe, hcost⟩ := hs
  have hresvsum : 0 ≤ ∑ i, s.resv i := Finset.sum_nonneg (fun i _ => hresv0 i)
  refine ⟨fun i hi => ⟨(hempty i hi).1, (hempty i hi).2.2.1⟩, hbdisj, ?_, hcash0,
    show (0:ℝ) ≤ s.bank + ∑ i, s.resv i by linarith, ?_, hshare, ?_, ?_⟩
  · -- the sold goods are disjoint from every bundle
    intro i
    refine Finset.disjoint_left.mpr (fun x hx hxb => ?_)
    simp only [CStage.toStage, CStage.soldSet, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at hx
    obtain ⟨k, hk⟩ := hx
    exact Finset.disjoint_left.mp (hcb k i) hk hxb
  · show (∑ i, s.cash i) + (s.bank + ∑ i, s.resv i) = ∑ g ∈ s.soldSet, p g
    linarith
  · -- safety
    intro i hi j
    have h := hsafe i hi j
    have hreq : s.req v p eps j ≤ (s.toStage).guar v p j + eps := by
      unfold CStage.req GeneralTPS.Stage.guar
      by_cases hj : j ∈ s.served <;> (simp [hj, CStage.toStage]; try linarith)
    rcases h with h | ⟨h1, h2, h3⟩
    · exact Or.inl (le_trans h hreq)
    · exact Or.inr ⟨h1, h2, fun g hg => le_trans (h3 g hg) hreq⟩
  · -- the counting invariant
    intro j hj
    have := counting_of_cost v p eps hn hp
      ⟨hempty, hbdisj, hcdisj, hcb, hcash0, hresv0, hbank0, hmoney, hshare, hsafe, hcost⟩ j hj
    show (2 * ((n : ℝ) - (s.served.card : ℝ)) - 1) * GeneralTPS.thr v p j
      ≤ truncBundle (v j) p (TPS n (v j) p) s.pool + (s.bank + ∑ i, s.resv i)
    linarith
end FairSelling.ChargeTPS
